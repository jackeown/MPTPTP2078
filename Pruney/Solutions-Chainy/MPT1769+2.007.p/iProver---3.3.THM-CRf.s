%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:02 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :  225 (16814 expanded)
%              Number of clauses        :  122 (2125 expanded)
%              Number of leaves         :   23 (7383 expanded)
%              Depth                    :   26
%              Number of atoms          : 1330 (366497 expanded)
%              Number of equality atoms :  429 (22611 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   50 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) ),
    inference(cnf_transformation,[],[f56])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(nnf_transformation,[],[f34])).

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
          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK8),X5) )
        & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
          | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK8),X5) )
        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK8)
        & X0 = X3
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK8,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK8) ) ) ),
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
            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK7)
              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK7) )
            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK7)
              | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK7) )
            & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
            & X0 = X3
            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X6) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK7,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
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
                ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK6,X2),X5)
                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK6,X2),X5)
                  | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK6,X6)
                & X0 = X3
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X6) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
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
                      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK5,X2,X6),X5) )
                    & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK5,X2,X6),X5) )
                    & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK5),u1_struct_0(X1),X4,X6)
                    & sK5 = X0
                    & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                    & v1_funct_2(X6,u1_struct_0(sK5),u1_struct_0(X1))
                    & v1_funct_1(X6) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
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
                        ( ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK4),X5)
                          | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,X6),X5) )
                        & ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK4),X5)
                          | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,X6),X5) )
                        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                        & X0 = X3
                        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X6) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                    & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
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
                            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X4,X2),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X3,X2,X6),X5) )
                            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X4,X2),X5)
                              | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X3,X2,X6),X5) )
                            & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK3),u1_struct_0(X3),u1_struct_0(sK3),X4,X6)
                            & X0 = X3
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK3))
                            & v1_funct_1(X6) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
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
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK2,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK2,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & sK2 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
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

fof(f56,plain,
    ( ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7)
      | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) )
    & ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7)
      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) )
    & r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8)
    & sK2 = sK5
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f48,f55,f54,f53,f52,f51,f50,f49])).

fof(f99,plain,(
    sK2 = sK5 ),
    inference(cnf_transformation,[],[f56])).

fof(f106,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK5,sK3,sK5,sK4,sK8),sK7) ),
    inference(definition_unfolding,[],[f101,f99,f99])).

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

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f95,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f9,axiom,(
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

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

fof(f70,plain,(
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

fof(f93,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f94,plain,(
    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f83,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f84,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f85,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

fof(f72,plain,(
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

fof(f100,plain,(
    r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8) ),
    inference(cnf_transformation,[],[f56])).

fof(f107,plain,(
    r1_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8) ),
    inference(definition_unfolding,[],[f100,f99])).

fof(f90,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f109,plain,(
    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(definition_unfolding,[],[f91,f99])).

fof(f92,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f108,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f92,f99])).

fof(f96,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f56])).

fof(f97,plain,(
    v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f98,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f58,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f65])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f103,plain,(
    ! [X0] : ~ v1_xboole_0(k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f66,f65])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f87,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f111,plain,(
    m1_pre_topc(sK4,sK5) ),
    inference(definition_unfolding,[],[f87,f99])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f28])).

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
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
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
    inference(flattening,[],[f25])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
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
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f114,plain,(
    ~ v2_struct_0(sK5) ),
    inference(definition_unfolding,[],[f80,f99])).

fof(f81,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f113,plain,(
    v2_pre_topc(sK5) ),
    inference(definition_unfolding,[],[f81,f99])).

fof(f82,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f112,plain,(
    l1_pre_topc(sK5) ),
    inference(definition_unfolding,[],[f82,f99])).

fof(f89,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f110,plain,(
    m1_pre_topc(sK5,sK5) ),
    inference(definition_unfolding,[],[f89,f99])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f102,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7)
    | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f105,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7)
    | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK5,sK3,sK5,sK4,sK8),sK7) ),
    inference(definition_unfolding,[],[f102,f99,f99])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f71])).

cnf(c_23,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK5,sK3,sK5,sK4,sK8),sK7)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1895,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK5,sK3,sK5,sK4,sK8),sK7) = iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1900,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | m1_pre_topc(X3,X4) != iProver_top
    | m1_pre_topc(X1,X4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X4) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X4) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1891,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_13,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1903,plain,
    ( X0 = X1
    | r2_funct_2(X2,X3,X1,X0) != iProver_top
    | v1_funct_2(X0,X2,X3) != iProver_top
    | v1_funct_2(X1,X2,X3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4282,plain,
    ( sK7 = X0
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0,sK7) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1891,c_1903])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_57,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_58,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4620,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | sK7 = X0
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0,sK7) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4282,c_57,c_58])).

cnf(c_4621,plain,
    ( sK7 = X0
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0,sK7) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4620])).

cnf(c_4627,plain,
    ( k3_tmap_1(X0,sK3,X1,sK4,X2) = sK7
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X1,sK4,X2),sK7) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0,sK3,X1,sK4,X2),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k3_tmap_1(X0,sK3,X1,sK4,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1900,c_4621])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_47,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_48,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_49,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_6840,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | v1_funct_2(k3_tmap_1(X0,sK3,X1,sK4,X2),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X1,sK4,X2),sK7) != iProver_top
    | k3_tmap_1(X0,sK3,X1,sK4,X2) = sK7
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k3_tmap_1(X0,sK3,X1,sK4,X2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4627,c_47,c_48,c_49])).

cnf(c_6841,plain,
    ( k3_tmap_1(X0,sK3,X1,sK4,X2) = sK7
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X1,sK4,X2),sK7) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0,sK3,X1,sK4,X2),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k3_tmap_1(X0,sK3,X1,sK4,X2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6840])).

cnf(c_6844,plain,
    ( k3_tmap_1(sK5,sK3,sK5,sK4,sK8) = sK7
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) = iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK3,sK5,sK4,sK8),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | m1_pre_topc(sK4,sK5) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK3,sK5,sK4,sK8)) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1895,c_6841])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1912,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_15,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | X4 = X5 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_24,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_546,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | X3 = X0
    | u1_struct_0(sK5) != X4
    | u1_struct_0(sK5) != X1
    | u1_struct_0(sK3) != X5
    | u1_struct_0(sK3) != X2
    | sK8 != X3
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_547,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK3))
    | sK8 = sK6 ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_549,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | sK8 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_547,c_33,c_32,c_31,c_27,c_26,c_25])).

cnf(c_1876,plain,
    ( sK8 = sK6
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_549])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1915,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1907,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1905,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3804,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(k2_tarski(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1907,c_1905])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_101,plain,
    ( v1_xboole_0(k2_tarski(X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5166,plain,
    ( v1_xboole_0(X2) != iProver_top
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3804,c_101])).

cnf(c_5167,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5166])).

cnf(c_5172,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1915,c_5167])).

cnf(c_1894,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1906,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3886,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1894,c_1906])).

cnf(c_5184,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5172,c_3886])).

cnf(c_5701,plain,
    ( sK8 = sK6
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1876,c_5184])).

cnf(c_5889,plain,
    ( sK8 = sK6
    | r1_tarski(sK8,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_5701])).

cnf(c_1888,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3888,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1888,c_1906])).

cnf(c_5183,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5172,c_3888])).

cnf(c_5545,plain,
    ( sK8 = sK6
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1876,c_5183])).

cnf(c_5690,plain,
    ( sK8 = sK6
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_5545])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1910,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6027,plain,
    ( sK8 = sK6
    | sK6 = X0
    | r1_tarski(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5690,c_1910])).

cnf(c_6193,plain,
    ( sK8 = sK6 ),
    inference(superposition,[status(thm)],[c_5889,c_6027])).

cnf(c_36,negated_conjecture,
    ( m1_pre_topc(sK4,sK5) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1883,plain,
    ( m1_pre_topc(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1901,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X4) != iProver_top
    | m1_pre_topc(X0,X4) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X4) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4386,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK5,X0,sK8)
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top
    | m1_pre_topc(sK5,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1894,c_1901])).

cnf(c_60,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_61,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5116,plain,
    ( v2_pre_topc(X1) != iProver_top
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK5,X0,sK8)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top
    | m1_pre_topc(sK5,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4386,c_47,c_48,c_49,c_60,c_61])).

cnf(c_5117,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK5,X0,sK8)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top
    | m1_pre_topc(sK5,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5116])).

cnf(c_5123,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK8,u1_struct_0(sK4)) = k3_tmap_1(sK5,sK3,sK5,sK4,sK8)
    | m1_pre_topc(sK5,sK5) != iProver_top
    | m1_pre_topc(sK4,sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1883,c_5117])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1902,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4315,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k2_tmap_1(sK5,sK3,sK8,X0)
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1894,c_1902])).

cnf(c_43,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_44,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_45,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_46,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_4725,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k2_tmap_1(sK5,sK3,sK8,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4315,c_44,c_45,c_46,c_47,c_48,c_49,c_60,c_61])).

cnf(c_4726,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k2_tmap_1(sK5,sK3,sK8,X0)
    | m1_pre_topc(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_4725])).

cnf(c_4732,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK8,u1_struct_0(sK4)) = k2_tmap_1(sK5,sK3,sK8,sK4) ),
    inference(superposition,[status(thm)],[c_1883,c_4726])).

cnf(c_5124,plain,
    ( k3_tmap_1(sK5,sK3,sK5,sK4,sK8) = k2_tmap_1(sK5,sK3,sK8,sK4)
    | m1_pre_topc(sK5,sK5) != iProver_top
    | m1_pre_topc(sK4,sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5123,c_4732])).

cnf(c_51,plain,
    ( m1_pre_topc(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_34,negated_conjecture,
    ( m1_pre_topc(sK5,sK5) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_53,plain,
    ( m1_pre_topc(sK5,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_6520,plain,
    ( k3_tmap_1(sK5,sK3,sK5,sK4,sK8) = k2_tmap_1(sK5,sK3,sK8,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5124,c_44,c_45,c_46,c_51,c_53])).

cnf(c_6522,plain,
    ( k3_tmap_1(sK5,sK3,sK5,sK4,sK6) = k2_tmap_1(sK5,sK3,sK6,sK4) ),
    inference(light_normalisation,[status(thm)],[c_6520,c_6193])).

cnf(c_6848,plain,
    ( k2_tmap_1(sK5,sK3,sK6,sK4) = sK7
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) = iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | m1_pre_topc(sK4,sK5) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3,sK6,sK4)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6844,c_6193,c_6522])).

cnf(c_54,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_55,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_56,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1899,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2)) = iProver_top
    | m1_pre_topc(X4,X3) != iProver_top
    | m1_pre_topc(X1,X3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6524,plain,
    ( v1_funct_2(k2_tmap_1(sK5,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | m1_pre_topc(sK4,sK5) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6522,c_1899])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1898,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | m1_pre_topc(X3,X4) != iProver_top
    | m1_pre_topc(X1,X4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X4) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X4) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3685,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK5,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k3_tmap_1(X1,sK3,sK5,X0,sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1888,c_1898])).

cnf(c_5109,plain,
    ( v1_funct_1(k3_tmap_1(X1,sK3,sK5,X0,sK6)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK5,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3685,c_47,c_48,c_49,c_54,c_55])).

cnf(c_5110,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK5,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1,sK3,sK5,X0,sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5109])).

cnf(c_6525,plain,
    ( m1_pre_topc(sK5,sK5) != iProver_top
    | m1_pre_topc(sK4,sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3,sK6,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6522,c_5110])).

cnf(c_6845,plain,
    ( k3_tmap_1(sK5,sK3,sK5,sK4,sK6) = sK7
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK3,sK5,sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | m1_pre_topc(sK4,sK5) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK3,sK5,sK4,sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6522,c_6841])).

cnf(c_6846,plain,
    ( k3_tmap_1(sK5,sK3,sK5,sK4,sK6) = sK7
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | m1_pre_topc(sK4,sK5) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3,sK6,sK4)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6845,c_6522])).

cnf(c_6847,plain,
    ( k2_tmap_1(sK5,sK3,sK6,sK4) = sK7
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | m1_pre_topc(sK4,sK5) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3,sK6,sK4)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6846,c_6522])).

cnf(c_6852,plain,
    ( k2_tmap_1(sK5,sK3,sK6,sK4) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6848,c_44,c_45,c_46,c_47,c_48,c_49,c_51,c_53,c_54,c_55,c_56,c_6524,c_6525,c_6847])).

cnf(c_6855,plain,
    ( k3_tmap_1(sK5,sK3,sK5,sK4,sK6) = sK7 ),
    inference(demodulation,[status(thm)],[c_6852,c_6522])).

cnf(c_22,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK5,sK3,sK5,sK4,sK8),sK7)
    | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1896,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK5,sK3,sK5,sK4,sK8),sK7) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6858,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK5,sK3,sK5,sK4,sK8),sK7) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK7,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6852,c_1896])).

cnf(c_6859,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK5,sK3,sK5,sK4,sK6),sK7) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK7,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6858,c_6193])).

cnf(c_6860,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK7,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6855,c_6859])).

cnf(c_12,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1904,plain,
    ( r2_funct_2(X0,X1,X2,X2) = iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3901,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK7,sK7) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1891,c_1904])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6860,c_3901,c_58,c_57])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:05:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.67/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/0.98  
% 3.67/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.67/0.98  
% 3.67/0.98  ------  iProver source info
% 3.67/0.98  
% 3.67/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.67/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.67/0.98  git: non_committed_changes: false
% 3.67/0.98  git: last_make_outside_of_git: false
% 3.67/0.98  
% 3.67/0.98  ------ 
% 3.67/0.98  
% 3.67/0.98  ------ Input Options
% 3.67/0.98  
% 3.67/0.98  --out_options                           all
% 3.67/0.98  --tptp_safe_out                         true
% 3.67/0.98  --problem_path                          ""
% 3.67/0.98  --include_path                          ""
% 3.67/0.98  --clausifier                            res/vclausify_rel
% 3.67/0.98  --clausifier_options                    ""
% 3.67/0.98  --stdin                                 false
% 3.67/0.98  --stats_out                             all
% 3.67/0.98  
% 3.67/0.98  ------ General Options
% 3.67/0.98  
% 3.67/0.98  --fof                                   false
% 3.67/0.98  --time_out_real                         305.
% 3.67/0.98  --time_out_virtual                      -1.
% 3.67/0.98  --symbol_type_check                     false
% 3.67/0.98  --clausify_out                          false
% 3.67/0.98  --sig_cnt_out                           false
% 3.67/0.98  --trig_cnt_out                          false
% 3.67/0.98  --trig_cnt_out_tolerance                1.
% 3.67/0.98  --trig_cnt_out_sk_spl                   false
% 3.67/0.98  --abstr_cl_out                          false
% 3.67/0.98  
% 3.67/0.98  ------ Global Options
% 3.67/0.98  
% 3.67/0.98  --schedule                              default
% 3.67/0.98  --add_important_lit                     false
% 3.67/0.98  --prop_solver_per_cl                    1000
% 3.67/0.98  --min_unsat_core                        false
% 3.67/0.98  --soft_assumptions                      false
% 3.67/0.98  --soft_lemma_size                       3
% 3.67/0.98  --prop_impl_unit_size                   0
% 3.67/0.98  --prop_impl_unit                        []
% 3.67/0.98  --share_sel_clauses                     true
% 3.67/0.98  --reset_solvers                         false
% 3.67/0.98  --bc_imp_inh                            [conj_cone]
% 3.67/0.98  --conj_cone_tolerance                   3.
% 3.67/0.98  --extra_neg_conj                        none
% 3.67/0.98  --large_theory_mode                     true
% 3.67/0.98  --prolific_symb_bound                   200
% 3.67/0.98  --lt_threshold                          2000
% 3.67/0.98  --clause_weak_htbl                      true
% 3.67/0.98  --gc_record_bc_elim                     false
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing Options
% 3.67/0.98  
% 3.67/0.98  --preprocessing_flag                    true
% 3.67/0.98  --time_out_prep_mult                    0.1
% 3.67/0.98  --splitting_mode                        input
% 3.67/0.98  --splitting_grd                         true
% 3.67/0.98  --splitting_cvd                         false
% 3.67/0.98  --splitting_cvd_svl                     false
% 3.67/0.98  --splitting_nvd                         32
% 3.67/0.98  --sub_typing                            true
% 3.67/0.98  --prep_gs_sim                           true
% 3.67/0.98  --prep_unflatten                        true
% 3.67/0.98  --prep_res_sim                          true
% 3.67/0.98  --prep_upred                            true
% 3.67/0.98  --prep_sem_filter                       exhaustive
% 3.67/0.98  --prep_sem_filter_out                   false
% 3.67/0.98  --pred_elim                             true
% 3.67/0.98  --res_sim_input                         true
% 3.67/0.98  --eq_ax_congr_red                       true
% 3.67/0.98  --pure_diseq_elim                       true
% 3.67/0.98  --brand_transform                       false
% 3.67/0.98  --non_eq_to_eq                          false
% 3.67/0.98  --prep_def_merge                        true
% 3.67/0.98  --prep_def_merge_prop_impl              false
% 3.67/0.98  --prep_def_merge_mbd                    true
% 3.67/0.98  --prep_def_merge_tr_red                 false
% 3.67/0.98  --prep_def_merge_tr_cl                  false
% 3.67/0.98  --smt_preprocessing                     true
% 3.67/0.98  --smt_ac_axioms                         fast
% 3.67/0.98  --preprocessed_out                      false
% 3.67/0.98  --preprocessed_stats                    false
% 3.67/0.98  
% 3.67/0.98  ------ Abstraction refinement Options
% 3.67/0.98  
% 3.67/0.98  --abstr_ref                             []
% 3.67/0.98  --abstr_ref_prep                        false
% 3.67/0.98  --abstr_ref_until_sat                   false
% 3.67/0.98  --abstr_ref_sig_restrict                funpre
% 3.67/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/0.98  --abstr_ref_under                       []
% 3.67/0.98  
% 3.67/0.98  ------ SAT Options
% 3.67/0.98  
% 3.67/0.98  --sat_mode                              false
% 3.67/0.98  --sat_fm_restart_options                ""
% 3.67/0.98  --sat_gr_def                            false
% 3.67/0.98  --sat_epr_types                         true
% 3.67/0.98  --sat_non_cyclic_types                  false
% 3.67/0.98  --sat_finite_models                     false
% 3.67/0.98  --sat_fm_lemmas                         false
% 3.67/0.98  --sat_fm_prep                           false
% 3.67/0.98  --sat_fm_uc_incr                        true
% 3.67/0.98  --sat_out_model                         small
% 3.67/0.98  --sat_out_clauses                       false
% 3.67/0.98  
% 3.67/0.98  ------ QBF Options
% 3.67/0.98  
% 3.67/0.98  --qbf_mode                              false
% 3.67/0.98  --qbf_elim_univ                         false
% 3.67/0.98  --qbf_dom_inst                          none
% 3.67/0.98  --qbf_dom_pre_inst                      false
% 3.67/0.98  --qbf_sk_in                             false
% 3.67/0.98  --qbf_pred_elim                         true
% 3.67/0.98  --qbf_split                             512
% 3.67/0.98  
% 3.67/0.98  ------ BMC1 Options
% 3.67/0.98  
% 3.67/0.98  --bmc1_incremental                      false
% 3.67/0.98  --bmc1_axioms                           reachable_all
% 3.67/0.98  --bmc1_min_bound                        0
% 3.67/0.98  --bmc1_max_bound                        -1
% 3.67/0.98  --bmc1_max_bound_default                -1
% 3.67/0.98  --bmc1_symbol_reachability              true
% 3.67/0.98  --bmc1_property_lemmas                  false
% 3.67/0.98  --bmc1_k_induction                      false
% 3.67/0.98  --bmc1_non_equiv_states                 false
% 3.67/0.98  --bmc1_deadlock                         false
% 3.67/0.98  --bmc1_ucm                              false
% 3.67/0.98  --bmc1_add_unsat_core                   none
% 3.67/0.98  --bmc1_unsat_core_children              false
% 3.67/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/0.98  --bmc1_out_stat                         full
% 3.67/0.98  --bmc1_ground_init                      false
% 3.67/0.98  --bmc1_pre_inst_next_state              false
% 3.67/0.98  --bmc1_pre_inst_state                   false
% 3.67/0.98  --bmc1_pre_inst_reach_state             false
% 3.67/0.98  --bmc1_out_unsat_core                   false
% 3.67/0.98  --bmc1_aig_witness_out                  false
% 3.67/0.98  --bmc1_verbose                          false
% 3.67/0.98  --bmc1_dump_clauses_tptp                false
% 3.67/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.67/0.98  --bmc1_dump_file                        -
% 3.67/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.67/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.67/0.98  --bmc1_ucm_extend_mode                  1
% 3.67/0.98  --bmc1_ucm_init_mode                    2
% 3.67/0.98  --bmc1_ucm_cone_mode                    none
% 3.67/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.67/0.98  --bmc1_ucm_relax_model                  4
% 3.67/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.67/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/0.98  --bmc1_ucm_layered_model                none
% 3.67/0.98  --bmc1_ucm_max_lemma_size               10
% 3.67/0.98  
% 3.67/0.98  ------ AIG Options
% 3.67/0.98  
% 3.67/0.98  --aig_mode                              false
% 3.67/0.98  
% 3.67/0.98  ------ Instantiation Options
% 3.67/0.98  
% 3.67/0.98  --instantiation_flag                    true
% 3.67/0.98  --inst_sos_flag                         true
% 3.67/0.98  --inst_sos_phase                        true
% 3.67/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/0.98  --inst_lit_sel_side                     num_symb
% 3.67/0.98  --inst_solver_per_active                1400
% 3.67/0.98  --inst_solver_calls_frac                1.
% 3.67/0.98  --inst_passive_queue_type               priority_queues
% 3.67/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/0.98  --inst_passive_queues_freq              [25;2]
% 3.67/0.98  --inst_dismatching                      true
% 3.67/0.98  --inst_eager_unprocessed_to_passive     true
% 3.67/0.98  --inst_prop_sim_given                   true
% 3.67/0.98  --inst_prop_sim_new                     false
% 3.67/0.98  --inst_subs_new                         false
% 3.67/0.98  --inst_eq_res_simp                      false
% 3.67/0.98  --inst_subs_given                       false
% 3.67/0.98  --inst_orphan_elimination               true
% 3.67/0.98  --inst_learning_loop_flag               true
% 3.67/0.98  --inst_learning_start                   3000
% 3.67/0.98  --inst_learning_factor                  2
% 3.67/0.98  --inst_start_prop_sim_after_learn       3
% 3.67/0.98  --inst_sel_renew                        solver
% 3.67/0.98  --inst_lit_activity_flag                true
% 3.67/0.98  --inst_restr_to_given                   false
% 3.67/0.98  --inst_activity_threshold               500
% 3.67/0.98  --inst_out_proof                        true
% 3.67/0.98  
% 3.67/0.98  ------ Resolution Options
% 3.67/0.98  
% 3.67/0.98  --resolution_flag                       true
% 3.67/0.98  --res_lit_sel                           adaptive
% 3.67/0.98  --res_lit_sel_side                      none
% 3.67/0.98  --res_ordering                          kbo
% 3.67/0.98  --res_to_prop_solver                    active
% 3.67/0.98  --res_prop_simpl_new                    false
% 3.67/0.98  --res_prop_simpl_given                  true
% 3.67/0.98  --res_passive_queue_type                priority_queues
% 3.67/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/0.98  --res_passive_queues_freq               [15;5]
% 3.67/0.98  --res_forward_subs                      full
% 3.67/0.98  --res_backward_subs                     full
% 3.67/0.98  --res_forward_subs_resolution           true
% 3.67/0.98  --res_backward_subs_resolution          true
% 3.67/0.98  --res_orphan_elimination                true
% 3.67/0.98  --res_time_limit                        2.
% 3.67/0.98  --res_out_proof                         true
% 3.67/0.98  
% 3.67/0.98  ------ Superposition Options
% 3.67/0.98  
% 3.67/0.98  --superposition_flag                    true
% 3.67/0.98  --sup_passive_queue_type                priority_queues
% 3.67/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.67/0.98  --demod_completeness_check              fast
% 3.67/0.98  --demod_use_ground                      true
% 3.67/0.98  --sup_to_prop_solver                    passive
% 3.67/0.98  --sup_prop_simpl_new                    true
% 3.67/0.98  --sup_prop_simpl_given                  true
% 3.67/0.98  --sup_fun_splitting                     true
% 3.67/0.98  --sup_smt_interval                      50000
% 3.67/0.98  
% 3.67/0.98  ------ Superposition Simplification Setup
% 3.67/0.98  
% 3.67/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.67/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.67/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.67/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.67/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.67/0.98  --sup_immed_triv                        [TrivRules]
% 3.67/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.98  --sup_immed_bw_main                     []
% 3.67/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.67/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.98  --sup_input_bw                          []
% 3.67/0.98  
% 3.67/0.98  ------ Combination Options
% 3.67/0.98  
% 3.67/0.98  --comb_res_mult                         3
% 3.67/0.98  --comb_sup_mult                         2
% 3.67/0.98  --comb_inst_mult                        10
% 3.67/0.98  
% 3.67/0.98  ------ Debug Options
% 3.67/0.98  
% 3.67/0.98  --dbg_backtrace                         false
% 3.67/0.98  --dbg_dump_prop_clauses                 false
% 3.67/0.98  --dbg_dump_prop_clauses_file            -
% 3.67/0.98  --dbg_out_stat                          false
% 3.67/0.98  ------ Parsing...
% 3.67/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  ------ Proving...
% 3.67/0.98  ------ Problem Properties 
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  clauses                                 40
% 3.67/0.98  conjectures                             20
% 3.67/0.98  EPR                                     17
% 3.67/0.98  Horn                                    31
% 3.67/0.98  unary                                   20
% 3.67/0.98  binary                                  8
% 3.67/0.98  lits                                    125
% 3.67/0.98  lits eq                                 5
% 3.67/0.98  fd_pure                                 0
% 3.67/0.98  fd_pseudo                               0
% 3.67/0.98  fd_cond                                 0
% 3.67/0.98  fd_pseudo_cond                          2
% 3.67/0.98  AC symbols                              0
% 3.67/0.98  
% 3.67/0.98  ------ Schedule dynamic 5 is on 
% 3.67/0.98  
% 3.67/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ 
% 3.67/0.98  Current options:
% 3.67/0.98  ------ 
% 3.67/0.98  
% 3.67/0.98  ------ Input Options
% 3.67/0.98  
% 3.67/0.98  --out_options                           all
% 3.67/0.98  --tptp_safe_out                         true
% 3.67/0.98  --problem_path                          ""
% 3.67/0.98  --include_path                          ""
% 3.67/0.98  --clausifier                            res/vclausify_rel
% 3.67/0.98  --clausifier_options                    ""
% 3.67/0.98  --stdin                                 false
% 3.67/0.98  --stats_out                             all
% 3.67/0.98  
% 3.67/0.98  ------ General Options
% 3.67/0.98  
% 3.67/0.98  --fof                                   false
% 3.67/0.98  --time_out_real                         305.
% 3.67/0.98  --time_out_virtual                      -1.
% 3.67/0.98  --symbol_type_check                     false
% 3.67/0.98  --clausify_out                          false
% 3.67/0.98  --sig_cnt_out                           false
% 3.67/0.98  --trig_cnt_out                          false
% 3.67/0.98  --trig_cnt_out_tolerance                1.
% 3.67/0.98  --trig_cnt_out_sk_spl                   false
% 3.67/0.98  --abstr_cl_out                          false
% 3.67/0.98  
% 3.67/0.98  ------ Global Options
% 3.67/0.98  
% 3.67/0.98  --schedule                              default
% 3.67/0.98  --add_important_lit                     false
% 3.67/0.98  --prop_solver_per_cl                    1000
% 3.67/0.98  --min_unsat_core                        false
% 3.67/0.98  --soft_assumptions                      false
% 3.67/0.98  --soft_lemma_size                       3
% 3.67/0.98  --prop_impl_unit_size                   0
% 3.67/0.98  --prop_impl_unit                        []
% 3.67/0.98  --share_sel_clauses                     true
% 3.67/0.98  --reset_solvers                         false
% 3.67/0.98  --bc_imp_inh                            [conj_cone]
% 3.67/0.98  --conj_cone_tolerance                   3.
% 3.67/0.98  --extra_neg_conj                        none
% 3.67/0.98  --large_theory_mode                     true
% 3.67/0.98  --prolific_symb_bound                   200
% 3.67/0.98  --lt_threshold                          2000
% 3.67/0.98  --clause_weak_htbl                      true
% 3.67/0.98  --gc_record_bc_elim                     false
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing Options
% 3.67/0.98  
% 3.67/0.98  --preprocessing_flag                    true
% 3.67/0.98  --time_out_prep_mult                    0.1
% 3.67/0.98  --splitting_mode                        input
% 3.67/0.98  --splitting_grd                         true
% 3.67/0.98  --splitting_cvd                         false
% 3.67/0.98  --splitting_cvd_svl                     false
% 3.67/0.98  --splitting_nvd                         32
% 3.67/0.98  --sub_typing                            true
% 3.67/0.98  --prep_gs_sim                           true
% 3.67/0.98  --prep_unflatten                        true
% 3.67/0.98  --prep_res_sim                          true
% 3.67/0.98  --prep_upred                            true
% 3.67/0.98  --prep_sem_filter                       exhaustive
% 3.67/0.98  --prep_sem_filter_out                   false
% 3.67/0.98  --pred_elim                             true
% 3.67/0.98  --res_sim_input                         true
% 3.67/0.98  --eq_ax_congr_red                       true
% 3.67/0.98  --pure_diseq_elim                       true
% 3.67/0.98  --brand_transform                       false
% 3.67/0.98  --non_eq_to_eq                          false
% 3.67/0.98  --prep_def_merge                        true
% 3.67/0.98  --prep_def_merge_prop_impl              false
% 3.67/0.98  --prep_def_merge_mbd                    true
% 3.67/0.98  --prep_def_merge_tr_red                 false
% 3.67/0.98  --prep_def_merge_tr_cl                  false
% 3.67/0.98  --smt_preprocessing                     true
% 3.67/0.98  --smt_ac_axioms                         fast
% 3.67/0.98  --preprocessed_out                      false
% 3.67/0.98  --preprocessed_stats                    false
% 3.67/0.98  
% 3.67/0.98  ------ Abstraction refinement Options
% 3.67/0.98  
% 3.67/0.98  --abstr_ref                             []
% 3.67/0.98  --abstr_ref_prep                        false
% 3.67/0.98  --abstr_ref_until_sat                   false
% 3.67/0.98  --abstr_ref_sig_restrict                funpre
% 3.67/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/0.98  --abstr_ref_under                       []
% 3.67/0.98  
% 3.67/0.98  ------ SAT Options
% 3.67/0.98  
% 3.67/0.98  --sat_mode                              false
% 3.67/0.98  --sat_fm_restart_options                ""
% 3.67/0.98  --sat_gr_def                            false
% 3.67/0.98  --sat_epr_types                         true
% 3.67/0.98  --sat_non_cyclic_types                  false
% 3.67/0.98  --sat_finite_models                     false
% 3.67/0.98  --sat_fm_lemmas                         false
% 3.67/0.98  --sat_fm_prep                           false
% 3.67/0.98  --sat_fm_uc_incr                        true
% 3.67/0.98  --sat_out_model                         small
% 3.67/0.98  --sat_out_clauses                       false
% 3.67/0.98  
% 3.67/0.98  ------ QBF Options
% 3.67/0.98  
% 3.67/0.98  --qbf_mode                              false
% 3.67/0.98  --qbf_elim_univ                         false
% 3.67/0.98  --qbf_dom_inst                          none
% 3.67/0.98  --qbf_dom_pre_inst                      false
% 3.67/0.98  --qbf_sk_in                             false
% 3.67/0.98  --qbf_pred_elim                         true
% 3.67/0.98  --qbf_split                             512
% 3.67/0.98  
% 3.67/0.98  ------ BMC1 Options
% 3.67/0.98  
% 3.67/0.98  --bmc1_incremental                      false
% 3.67/0.98  --bmc1_axioms                           reachable_all
% 3.67/0.98  --bmc1_min_bound                        0
% 3.67/0.98  --bmc1_max_bound                        -1
% 3.67/0.98  --bmc1_max_bound_default                -1
% 3.67/0.98  --bmc1_symbol_reachability              true
% 3.67/0.98  --bmc1_property_lemmas                  false
% 3.67/0.98  --bmc1_k_induction                      false
% 3.67/0.98  --bmc1_non_equiv_states                 false
% 3.67/0.98  --bmc1_deadlock                         false
% 3.67/0.98  --bmc1_ucm                              false
% 3.67/0.98  --bmc1_add_unsat_core                   none
% 3.67/0.98  --bmc1_unsat_core_children              false
% 3.67/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/0.98  --bmc1_out_stat                         full
% 3.67/0.98  --bmc1_ground_init                      false
% 3.67/0.98  --bmc1_pre_inst_next_state              false
% 3.67/0.98  --bmc1_pre_inst_state                   false
% 3.67/0.98  --bmc1_pre_inst_reach_state             false
% 3.67/0.98  --bmc1_out_unsat_core                   false
% 3.67/0.98  --bmc1_aig_witness_out                  false
% 3.67/0.98  --bmc1_verbose                          false
% 3.67/0.98  --bmc1_dump_clauses_tptp                false
% 3.67/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.67/0.98  --bmc1_dump_file                        -
% 3.67/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.67/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.67/0.98  --bmc1_ucm_extend_mode                  1
% 3.67/0.98  --bmc1_ucm_init_mode                    2
% 3.67/0.98  --bmc1_ucm_cone_mode                    none
% 3.67/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.67/0.98  --bmc1_ucm_relax_model                  4
% 3.67/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.67/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/0.98  --bmc1_ucm_layered_model                none
% 3.67/0.98  --bmc1_ucm_max_lemma_size               10
% 3.67/0.98  
% 3.67/0.98  ------ AIG Options
% 3.67/0.98  
% 3.67/0.98  --aig_mode                              false
% 3.67/0.98  
% 3.67/0.98  ------ Instantiation Options
% 3.67/0.98  
% 3.67/0.98  --instantiation_flag                    true
% 3.67/0.98  --inst_sos_flag                         true
% 3.67/0.98  --inst_sos_phase                        true
% 3.67/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/0.98  --inst_lit_sel_side                     none
% 3.67/0.98  --inst_solver_per_active                1400
% 3.67/0.98  --inst_solver_calls_frac                1.
% 3.67/0.98  --inst_passive_queue_type               priority_queues
% 3.67/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/0.98  --inst_passive_queues_freq              [25;2]
% 3.67/0.98  --inst_dismatching                      true
% 3.67/0.98  --inst_eager_unprocessed_to_passive     true
% 3.67/0.98  --inst_prop_sim_given                   true
% 3.67/0.98  --inst_prop_sim_new                     false
% 3.67/0.98  --inst_subs_new                         false
% 3.67/0.98  --inst_eq_res_simp                      false
% 3.67/0.98  --inst_subs_given                       false
% 3.67/0.98  --inst_orphan_elimination               true
% 3.67/0.98  --inst_learning_loop_flag               true
% 3.67/0.98  --inst_learning_start                   3000
% 3.67/0.98  --inst_learning_factor                  2
% 3.67/0.98  --inst_start_prop_sim_after_learn       3
% 3.67/0.98  --inst_sel_renew                        solver
% 3.67/0.98  --inst_lit_activity_flag                true
% 3.67/0.98  --inst_restr_to_given                   false
% 3.67/0.98  --inst_activity_threshold               500
% 3.67/0.98  --inst_out_proof                        true
% 3.67/0.98  
% 3.67/0.98  ------ Resolution Options
% 3.67/0.98  
% 3.67/0.98  --resolution_flag                       false
% 3.67/0.98  --res_lit_sel                           adaptive
% 3.67/0.98  --res_lit_sel_side                      none
% 3.67/0.98  --res_ordering                          kbo
% 3.67/0.98  --res_to_prop_solver                    active
% 3.67/0.98  --res_prop_simpl_new                    false
% 3.67/0.98  --res_prop_simpl_given                  true
% 3.67/0.98  --res_passive_queue_type                priority_queues
% 3.67/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/0.98  --res_passive_queues_freq               [15;5]
% 3.67/0.98  --res_forward_subs                      full
% 3.67/0.98  --res_backward_subs                     full
% 3.67/0.98  --res_forward_subs_resolution           true
% 3.67/0.98  --res_backward_subs_resolution          true
% 3.67/0.98  --res_orphan_elimination                true
% 3.67/0.98  --res_time_limit                        2.
% 3.67/0.98  --res_out_proof                         true
% 3.67/0.98  
% 3.67/0.98  ------ Superposition Options
% 3.67/0.98  
% 3.67/0.98  --superposition_flag                    true
% 3.67/0.98  --sup_passive_queue_type                priority_queues
% 3.67/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.67/0.98  --demod_completeness_check              fast
% 3.67/0.98  --demod_use_ground                      true
% 3.67/0.98  --sup_to_prop_solver                    passive
% 3.67/0.98  --sup_prop_simpl_new                    true
% 3.67/0.98  --sup_prop_simpl_given                  true
% 3.67/0.98  --sup_fun_splitting                     true
% 3.67/0.98  --sup_smt_interval                      50000
% 3.67/0.98  
% 3.67/0.98  ------ Superposition Simplification Setup
% 3.67/0.98  
% 3.67/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.67/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.67/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.67/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.67/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.67/0.98  --sup_immed_triv                        [TrivRules]
% 3.67/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.98  --sup_immed_bw_main                     []
% 3.67/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.67/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.98  --sup_input_bw                          []
% 3.67/0.98  
% 3.67/0.98  ------ Combination Options
% 3.67/0.98  
% 3.67/0.98  --comb_res_mult                         3
% 3.67/0.98  --comb_sup_mult                         2
% 3.67/0.98  --comb_inst_mult                        10
% 3.67/0.98  
% 3.67/0.98  ------ Debug Options
% 3.67/0.98  
% 3.67/0.98  --dbg_backtrace                         false
% 3.67/0.98  --dbg_dump_prop_clauses                 false
% 3.67/0.98  --dbg_dump_prop_clauses_file            -
% 3.67/0.98  --dbg_out_stat                          false
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  % SZS status Theorem for theBenchmark.p
% 3.67/0.98  
% 3.67/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.67/0.98  
% 3.67/0.98  fof(f101,plain,(
% 3.67/0.98    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f15,conjecture,(
% 3.67/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f16,negated_conjecture,(
% 3.67/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 3.67/0.98    inference(negated_conjecture,[],[f15])).
% 3.67/0.98  
% 3.67/0.98  fof(f33,plain,(
% 3.67/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.67/0.98    inference(ennf_transformation,[],[f16])).
% 3.67/0.98  
% 3.67/0.98  fof(f34,plain,(
% 3.67/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.67/0.98    inference(flattening,[],[f33])).
% 3.67/0.98  
% 3.67/0.98  fof(f47,plain,(
% 3.67/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.67/0.98    inference(nnf_transformation,[],[f34])).
% 3.67/0.98  
% 3.67/0.98  fof(f48,plain,(
% 3.67/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.67/0.98    inference(flattening,[],[f47])).
% 3.67/0.98  
% 3.67/0.98  fof(f55,plain,(
% 3.67/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK8),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK8),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK8) & X0 = X3 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK8,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK8))) )),
% 3.67/0.98    introduced(choice_axiom,[])).
% 3.67/0.98  
% 3.67/0.98  fof(f54,plain,(
% 3.67/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK7) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK7)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK7) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK7)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK7,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 3.67/0.98    introduced(choice_axiom,[])).
% 3.67/0.98  
% 3.67/0.98  fof(f53,plain,(
% 3.67/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK6,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK6,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK6,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 3.67/0.98    introduced(choice_axiom,[])).
% 3.67/0.98  
% 3.67/0.98  fof(f52,plain,(
% 3.67/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK5,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK5,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK5),u1_struct_0(X1),X4,X6) & sK5 = X0 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 3.67/0.98    introduced(choice_axiom,[])).
% 3.67/0.98  
% 3.67/0.98  fof(f51,plain,(
% 3.67/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK4),X5) | ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,X6),X5)) & (r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK4),X5) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.67/0.98    introduced(choice_axiom,[])).
% 3.67/0.98  
% 3.67/0.98  fof(f50,plain,(
% 3.67/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK3),u1_struct_0(X3),u1_struct_0(sK3),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 3.67/0.98    introduced(choice_axiom,[])).
% 3.67/0.98  
% 3.67/0.98  fof(f49,plain,(
% 3.67/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK2,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK2,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK2 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.67/0.98    introduced(choice_axiom,[])).
% 3.67/0.98  
% 3.67/0.98  fof(f56,plain,(
% 3.67/0.98    (((((((~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) | ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)) & (r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)) & r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8) & sK2 = sK5 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.67/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f48,f55,f54,f53,f52,f51,f50,f49])).
% 3.67/0.98  
% 3.67/0.98  fof(f99,plain,(
% 3.67/0.98    sK2 = sK5),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f106,plain,(
% 3.67/0.98    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK5,sK3,sK5,sK4,sK8),sK7)),
% 3.67/0.98    inference(definition_unfolding,[],[f101,f99,f99])).
% 3.67/0.98  
% 3.67/0.98  fof(f13,axiom,(
% 3.67/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f29,plain,(
% 3.67/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/0.98    inference(ennf_transformation,[],[f13])).
% 3.67/0.98  
% 3.67/0.98  fof(f30,plain,(
% 3.67/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.98    inference(flattening,[],[f29])).
% 3.67/0.98  
% 3.67/0.98  fof(f78,plain,(
% 3.67/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f30])).
% 3.67/0.98  
% 3.67/0.98  fof(f95,plain,(
% 3.67/0.98    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f9,axiom,(
% 3.67/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f21,plain,(
% 3.67/0.98    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.67/0.98    inference(ennf_transformation,[],[f9])).
% 3.67/0.98  
% 3.67/0.98  fof(f22,plain,(
% 3.67/0.98    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.67/0.98    inference(flattening,[],[f21])).
% 3.67/0.98  
% 3.67/0.98  fof(f45,plain,(
% 3.67/0.98    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.67/0.98    inference(nnf_transformation,[],[f22])).
% 3.67/0.98  
% 3.67/0.98  fof(f70,plain,(
% 3.67/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f45])).
% 3.67/0.98  
% 3.67/0.98  fof(f93,plain,(
% 3.67/0.98    v1_funct_1(sK7)),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f94,plain,(
% 3.67/0.98    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3))),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f83,plain,(
% 3.67/0.98    ~v2_struct_0(sK3)),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f84,plain,(
% 3.67/0.98    v2_pre_topc(sK3)),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f85,plain,(
% 3.67/0.98    l1_pre_topc(sK3)),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f2,axiom,(
% 3.67/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f17,plain,(
% 3.67/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.67/0.98    inference(ennf_transformation,[],[f2])).
% 3.67/0.98  
% 3.67/0.98  fof(f39,plain,(
% 3.67/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.67/0.98    inference(nnf_transformation,[],[f17])).
% 3.67/0.98  
% 3.67/0.98  fof(f40,plain,(
% 3.67/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.67/0.98    inference(rectify,[],[f39])).
% 3.67/0.98  
% 3.67/0.98  fof(f41,plain,(
% 3.67/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.67/0.98    introduced(choice_axiom,[])).
% 3.67/0.98  
% 3.67/0.98  fof(f42,plain,(
% 3.67/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.67/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).
% 3.67/0.98  
% 3.67/0.98  fof(f60,plain,(
% 3.67/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f42])).
% 3.67/0.98  
% 3.67/0.98  fof(f10,axiom,(
% 3.67/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f23,plain,(
% 3.67/0.98    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.67/0.98    inference(ennf_transformation,[],[f10])).
% 3.67/0.98  
% 3.67/0.98  fof(f24,plain,(
% 3.67/0.98    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.67/0.98    inference(flattening,[],[f23])).
% 3.67/0.98  
% 3.67/0.98  fof(f46,plain,(
% 3.67/0.98    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.67/0.98    inference(nnf_transformation,[],[f24])).
% 3.67/0.98  
% 3.67/0.98  fof(f72,plain,(
% 3.67/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f46])).
% 3.67/0.98  
% 3.67/0.98  fof(f100,plain,(
% 3.67/0.98    r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8)),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f107,plain,(
% 3.67/0.98    r1_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8)),
% 3.67/0.98    inference(definition_unfolding,[],[f100,f99])).
% 3.67/0.98  
% 3.67/0.98  fof(f90,plain,(
% 3.67/0.98    v1_funct_1(sK6)),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f91,plain,(
% 3.67/0.98    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f109,plain,(
% 3.67/0.98    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))),
% 3.67/0.98    inference(definition_unfolding,[],[f91,f99])).
% 3.67/0.98  
% 3.67/0.98  fof(f92,plain,(
% 3.67/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f108,plain,(
% 3.67/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 3.67/0.98    inference(definition_unfolding,[],[f92,f99])).
% 3.67/0.98  
% 3.67/0.98  fof(f96,plain,(
% 3.67/0.98    v1_funct_1(sK8)),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f97,plain,(
% 3.67/0.98    v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3))),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f98,plain,(
% 3.67/0.98    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f1,axiom,(
% 3.67/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f35,plain,(
% 3.67/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.67/0.98    inference(nnf_transformation,[],[f1])).
% 3.67/0.98  
% 3.67/0.98  fof(f36,plain,(
% 3.67/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.67/0.98    inference(rectify,[],[f35])).
% 3.67/0.98  
% 3.67/0.98  fof(f37,plain,(
% 3.67/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.67/0.98    introduced(choice_axiom,[])).
% 3.67/0.98  
% 3.67/0.98  fof(f38,plain,(
% 3.67/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.67/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 3.67/0.98  
% 3.67/0.98  fof(f58,plain,(
% 3.67/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f38])).
% 3.67/0.98  
% 3.67/0.98  fof(f6,axiom,(
% 3.67/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f18,plain,(
% 3.67/0.98    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 3.67/0.98    inference(ennf_transformation,[],[f6])).
% 3.67/0.98  
% 3.67/0.98  fof(f67,plain,(
% 3.67/0.98    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f18])).
% 3.67/0.98  
% 3.67/0.98  fof(f4,axiom,(
% 3.67/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f65,plain,(
% 3.67/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f4])).
% 3.67/0.98  
% 3.67/0.98  fof(f104,plain,(
% 3.67/0.98    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.67/0.98    inference(definition_unfolding,[],[f67,f65])).
% 3.67/0.98  
% 3.67/0.98  fof(f8,axiom,(
% 3.67/0.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f20,plain,(
% 3.67/0.98    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.67/0.98    inference(ennf_transformation,[],[f8])).
% 3.67/0.98  
% 3.67/0.98  fof(f69,plain,(
% 3.67/0.98    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f20])).
% 3.67/0.98  
% 3.67/0.98  fof(f5,axiom,(
% 3.67/0.98    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f66,plain,(
% 3.67/0.98    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.67/0.98    inference(cnf_transformation,[],[f5])).
% 3.67/0.98  
% 3.67/0.98  fof(f103,plain,(
% 3.67/0.98    ( ! [X0] : (~v1_xboole_0(k2_tarski(X0,X0))) )),
% 3.67/0.98    inference(definition_unfolding,[],[f66,f65])).
% 3.67/0.98  
% 3.67/0.98  fof(f7,axiom,(
% 3.67/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f19,plain,(
% 3.67/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.67/0.98    inference(ennf_transformation,[],[f7])).
% 3.67/0.98  
% 3.67/0.98  fof(f68,plain,(
% 3.67/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f19])).
% 3.67/0.98  
% 3.67/0.98  fof(f3,axiom,(
% 3.67/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f43,plain,(
% 3.67/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.67/0.98    inference(nnf_transformation,[],[f3])).
% 3.67/0.98  
% 3.67/0.98  fof(f44,plain,(
% 3.67/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.67/0.98    inference(flattening,[],[f43])).
% 3.67/0.98  
% 3.67/0.98  fof(f64,plain,(
% 3.67/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f44])).
% 3.67/0.98  
% 3.67/0.98  fof(f87,plain,(
% 3.67/0.98    m1_pre_topc(sK4,sK2)),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f111,plain,(
% 3.67/0.98    m1_pre_topc(sK4,sK5)),
% 3.67/0.98    inference(definition_unfolding,[],[f87,f99])).
% 3.67/0.98  
% 3.67/0.98  fof(f12,axiom,(
% 3.67/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f27,plain,(
% 3.67/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/0.98    inference(ennf_transformation,[],[f12])).
% 3.67/0.98  
% 3.67/0.98  fof(f28,plain,(
% 3.67/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.98    inference(flattening,[],[f27])).
% 3.67/0.98  
% 3.67/0.98  fof(f75,plain,(
% 3.67/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f28])).
% 3.67/0.98  
% 3.67/0.98  fof(f11,axiom,(
% 3.67/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f25,plain,(
% 3.67/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/0.98    inference(ennf_transformation,[],[f11])).
% 3.67/0.98  
% 3.67/0.98  fof(f26,plain,(
% 3.67/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.98    inference(flattening,[],[f25])).
% 3.67/0.98  
% 3.67/0.98  fof(f74,plain,(
% 3.67/0.98    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f26])).
% 3.67/0.98  
% 3.67/0.98  fof(f80,plain,(
% 3.67/0.98    ~v2_struct_0(sK2)),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f114,plain,(
% 3.67/0.98    ~v2_struct_0(sK5)),
% 3.67/0.98    inference(definition_unfolding,[],[f80,f99])).
% 3.67/0.98  
% 3.67/0.98  fof(f81,plain,(
% 3.67/0.98    v2_pre_topc(sK2)),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f113,plain,(
% 3.67/0.98    v2_pre_topc(sK5)),
% 3.67/0.98    inference(definition_unfolding,[],[f81,f99])).
% 3.67/0.98  
% 3.67/0.98  fof(f82,plain,(
% 3.67/0.98    l1_pre_topc(sK2)),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f112,plain,(
% 3.67/0.98    l1_pre_topc(sK5)),
% 3.67/0.98    inference(definition_unfolding,[],[f82,f99])).
% 3.67/0.98  
% 3.67/0.98  fof(f89,plain,(
% 3.67/0.98    m1_pre_topc(sK5,sK2)),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f110,plain,(
% 3.67/0.98    m1_pre_topc(sK5,sK5)),
% 3.67/0.98    inference(definition_unfolding,[],[f89,f99])).
% 3.67/0.98  
% 3.67/0.98  fof(f77,plain,(
% 3.67/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f30])).
% 3.67/0.98  
% 3.67/0.98  fof(f76,plain,(
% 3.67/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f30])).
% 3.67/0.98  
% 3.67/0.98  fof(f102,plain,(
% 3.67/0.98    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) | ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)),
% 3.67/0.98    inference(cnf_transformation,[],[f56])).
% 3.67/0.98  
% 3.67/0.98  fof(f105,plain,(
% 3.67/0.98    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) | ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK5,sK3,sK5,sK4,sK8),sK7)),
% 3.67/0.98    inference(definition_unfolding,[],[f102,f99,f99])).
% 3.67/0.98  
% 3.67/0.98  fof(f71,plain,(
% 3.67/0.98    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f45])).
% 3.67/0.98  
% 3.67/0.98  fof(f117,plain,(
% 3.67/0.98    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.67/0.98    inference(equality_resolution,[],[f71])).
% 3.67/0.98  
% 3.67/0.98  cnf(c_23,negated_conjecture,
% 3.67/0.98      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK5,sK3,sK5,sK4,sK8),sK7)
% 3.67/0.98      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) ),
% 3.67/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1895,plain,
% 3.67/0.98      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK5,sK3,sK5,sK4,sK8),sK7) = iProver_top
% 3.67/0.98      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_18,plain,
% 3.67/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.67/0.98      | ~ m1_pre_topc(X3,X4)
% 3.67/0.98      | ~ m1_pre_topc(X1,X4)
% 3.67/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.67/0.98      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 3.67/0.98      | v2_struct_0(X4)
% 3.67/0.98      | v2_struct_0(X2)
% 3.67/0.98      | ~ v2_pre_topc(X2)
% 3.67/0.98      | ~ v2_pre_topc(X4)
% 3.67/0.98      | ~ l1_pre_topc(X2)
% 3.67/0.98      | ~ l1_pre_topc(X4)
% 3.67/0.98      | ~ v1_funct_1(X0) ),
% 3.67/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1900,plain,
% 3.67/0.98      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.67/0.98      | m1_pre_topc(X3,X4) != iProver_top
% 3.67/0.98      | m1_pre_topc(X1,X4) != iProver_top
% 3.67/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.67/0.98      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) = iProver_top
% 3.67/0.98      | v2_struct_0(X4) = iProver_top
% 3.67/0.98      | v2_struct_0(X2) = iProver_top
% 3.67/0.98      | v2_pre_topc(X2) != iProver_top
% 3.67/0.98      | v2_pre_topc(X4) != iProver_top
% 3.67/0.98      | l1_pre_topc(X2) != iProver_top
% 3.67/0.98      | l1_pre_topc(X4) != iProver_top
% 3.67/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_28,negated_conjecture,
% 3.67/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 3.67/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1891,plain,
% 3.67/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_13,plain,
% 3.67/0.98      ( ~ r2_funct_2(X0,X1,X2,X3)
% 3.67/0.98      | ~ v1_funct_2(X3,X0,X1)
% 3.67/0.98      | ~ v1_funct_2(X2,X0,X1)
% 3.67/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.67/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.67/0.98      | ~ v1_funct_1(X3)
% 3.67/0.98      | ~ v1_funct_1(X2)
% 3.67/0.98      | X3 = X2 ),
% 3.67/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1903,plain,
% 3.67/0.98      ( X0 = X1
% 3.67/0.98      | r2_funct_2(X2,X3,X1,X0) != iProver_top
% 3.67/0.98      | v1_funct_2(X0,X2,X3) != iProver_top
% 3.67/0.98      | v1_funct_2(X1,X2,X3) != iProver_top
% 3.67/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.67/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.67/0.98      | v1_funct_1(X1) != iProver_top
% 3.67/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_4282,plain,
% 3.67/0.98      ( sK7 = X0
% 3.67/0.98      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0,sK7) != iProver_top
% 3.67/0.98      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.67/0.98      | v1_funct_1(X0) != iProver_top
% 3.67/0.98      | v1_funct_1(sK7) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_1891,c_1903]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_30,negated_conjecture,
% 3.67/0.98      ( v1_funct_1(sK7) ),
% 3.67/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_57,plain,
% 3.67/0.98      ( v1_funct_1(sK7) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_29,negated_conjecture,
% 3.67/0.98      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 3.67/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_58,plain,
% 3.67/0.98      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_4620,plain,
% 3.67/0.98      ( v1_funct_1(X0) != iProver_top
% 3.67/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.67/0.98      | sK7 = X0
% 3.67/0.98      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0,sK7) != iProver_top
% 3.67/0.98      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.67/0.98      inference(global_propositional_subsumption,
% 3.67/0.98                [status(thm)],
% 3.67/0.98                [c_4282,c_57,c_58]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_4621,plain,
% 3.67/0.98      ( sK7 = X0
% 3.67/0.98      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0,sK7) != iProver_top
% 3.67/0.98      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.67/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.67/0.98      inference(renaming,[status(thm)],[c_4620]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_4627,plain,
% 3.67/0.98      ( k3_tmap_1(X0,sK3,X1,sK4,X2) = sK7
% 3.67/0.98      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X1,sK4,X2),sK7) != iProver_top
% 3.67/0.98      | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | v1_funct_2(k3_tmap_1(X0,sK3,X1,sK4,X2),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | m1_pre_topc(X1,X0) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK4,X0) != iProver_top
% 3.67/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
% 3.67/0.98      | v2_struct_0(X0) = iProver_top
% 3.67/0.98      | v2_struct_0(sK3) = iProver_top
% 3.67/0.98      | v2_pre_topc(X0) != iProver_top
% 3.67/0.98      | v2_pre_topc(sK3) != iProver_top
% 3.67/0.98      | l1_pre_topc(X0) != iProver_top
% 3.67/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.67/0.98      | v1_funct_1(X2) != iProver_top
% 3.67/0.98      | v1_funct_1(k3_tmap_1(X0,sK3,X1,sK4,X2)) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_1900,c_4621]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_40,negated_conjecture,
% 3.67/0.98      ( ~ v2_struct_0(sK3) ),
% 3.67/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_47,plain,
% 3.67/0.98      ( v2_struct_0(sK3) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_39,negated_conjecture,
% 3.67/0.98      ( v2_pre_topc(sK3) ),
% 3.67/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_48,plain,
% 3.67/0.98      ( v2_pre_topc(sK3) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_38,negated_conjecture,
% 3.67/0.98      ( l1_pre_topc(sK3) ),
% 3.67/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_49,plain,
% 3.67/0.98      ( l1_pre_topc(sK3) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6840,plain,
% 3.67/0.98      ( l1_pre_topc(X0) != iProver_top
% 3.67/0.98      | v2_struct_0(X0) = iProver_top
% 3.67/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK4,X0) != iProver_top
% 3.67/0.98      | m1_pre_topc(X1,X0) != iProver_top
% 3.67/0.98      | v1_funct_2(k3_tmap_1(X0,sK3,X1,sK4,X2),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X1,sK4,X2),sK7) != iProver_top
% 3.67/0.98      | k3_tmap_1(X0,sK3,X1,sK4,X2) = sK7
% 3.67/0.98      | v2_pre_topc(X0) != iProver_top
% 3.67/0.98      | v1_funct_1(X2) != iProver_top
% 3.67/0.98      | v1_funct_1(k3_tmap_1(X0,sK3,X1,sK4,X2)) != iProver_top ),
% 3.67/0.98      inference(global_propositional_subsumption,
% 3.67/0.98                [status(thm)],
% 3.67/0.98                [c_4627,c_47,c_48,c_49]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6841,plain,
% 3.67/0.98      ( k3_tmap_1(X0,sK3,X1,sK4,X2) = sK7
% 3.67/0.98      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X1,sK4,X2),sK7) != iProver_top
% 3.67/0.98      | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | v1_funct_2(k3_tmap_1(X0,sK3,X1,sK4,X2),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | m1_pre_topc(X1,X0) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK4,X0) != iProver_top
% 3.67/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
% 3.67/0.98      | v2_struct_0(X0) = iProver_top
% 3.67/0.98      | v2_pre_topc(X0) != iProver_top
% 3.67/0.98      | l1_pre_topc(X0) != iProver_top
% 3.67/0.98      | v1_funct_1(X2) != iProver_top
% 3.67/0.98      | v1_funct_1(k3_tmap_1(X0,sK3,X1,sK4,X2)) != iProver_top ),
% 3.67/0.98      inference(renaming,[status(thm)],[c_6840]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6844,plain,
% 3.67/0.98      ( k3_tmap_1(sK5,sK3,sK5,sK4,sK8) = sK7
% 3.67/0.98      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) = iProver_top
% 3.67/0.98      | v1_funct_2(k3_tmap_1(sK5,sK3,sK5,sK4,sK8),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK5,sK5) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK4,sK5) != iProver_top
% 3.67/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.67/0.98      | v2_struct_0(sK5) = iProver_top
% 3.67/0.98      | v2_pre_topc(sK5) != iProver_top
% 3.67/0.98      | l1_pre_topc(sK5) != iProver_top
% 3.67/0.98      | v1_funct_1(k3_tmap_1(sK5,sK3,sK5,sK4,sK8)) != iProver_top
% 3.67/0.98      | v1_funct_1(sK8) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_1895,c_6841]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3,plain,
% 3.67/0.98      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.67/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1912,plain,
% 3.67/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.67/0.98      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_15,plain,
% 3.67/0.98      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 3.67/0.98      | ~ v1_funct_2(X5,X2,X3)
% 3.67/0.98      | ~ v1_funct_2(X4,X0,X1)
% 3.67/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.67/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.67/0.98      | ~ v1_funct_1(X5)
% 3.67/0.98      | ~ v1_funct_1(X4)
% 3.67/0.98      | v1_xboole_0(X1)
% 3.67/0.98      | v1_xboole_0(X3)
% 3.67/0.98      | X4 = X5 ),
% 3.67/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_24,negated_conjecture,
% 3.67/0.98      ( r1_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8) ),
% 3.67/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_546,plain,
% 3.67/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.67/0.98      | ~ v1_funct_2(X3,X4,X5)
% 3.67/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.67/0.98      | ~ v1_funct_1(X0)
% 3.67/0.98      | ~ v1_funct_1(X3)
% 3.67/0.98      | v1_xboole_0(X2)
% 3.67/0.98      | v1_xboole_0(X5)
% 3.67/0.98      | X3 = X0
% 3.67/0.98      | u1_struct_0(sK5) != X4
% 3.67/0.98      | u1_struct_0(sK5) != X1
% 3.67/0.98      | u1_struct_0(sK3) != X5
% 3.67/0.98      | u1_struct_0(sK3) != X2
% 3.67/0.98      | sK8 != X3
% 3.67/0.98      | sK6 != X0 ),
% 3.67/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_547,plain,
% 3.67/0.98      ( ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3))
% 3.67/0.98      | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
% 3.67/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.67/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.67/0.98      | ~ v1_funct_1(sK8)
% 3.67/0.98      | ~ v1_funct_1(sK6)
% 3.67/0.98      | v1_xboole_0(u1_struct_0(sK3))
% 3.67/0.98      | sK8 = sK6 ),
% 3.67/0.98      inference(unflattening,[status(thm)],[c_546]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_33,negated_conjecture,
% 3.67/0.98      ( v1_funct_1(sK6) ),
% 3.67/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_32,negated_conjecture,
% 3.67/0.98      ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 3.67/0.98      inference(cnf_transformation,[],[f109]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_31,negated_conjecture,
% 3.67/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 3.67/0.98      inference(cnf_transformation,[],[f108]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_27,negated_conjecture,
% 3.67/0.98      ( v1_funct_1(sK8) ),
% 3.67/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_26,negated_conjecture,
% 3.67/0.98      ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 3.67/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_25,negated_conjecture,
% 3.67/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 3.67/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_549,plain,
% 3.67/0.98      ( v1_xboole_0(u1_struct_0(sK3)) | sK8 = sK6 ),
% 3.67/0.98      inference(global_propositional_subsumption,
% 3.67/0.98                [status(thm)],
% 3.67/0.98                [c_547,c_33,c_32,c_31,c_27,c_26,c_25]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1876,plain,
% 3.67/0.98      ( sK8 = sK6 | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_549]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_0,plain,
% 3.67/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.67/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1915,plain,
% 3.67/0.98      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.67/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_9,plain,
% 3.67/0.98      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 3.67/0.98      | ~ r2_hidden(X0,X1) ),
% 3.67/0.98      inference(cnf_transformation,[],[f104]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1907,plain,
% 3.67/0.98      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.67/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_11,plain,
% 3.67/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.98      | ~ v1_xboole_0(X2)
% 3.67/0.98      | v1_xboole_0(X0) ),
% 3.67/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1905,plain,
% 3.67/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.67/0.98      | v1_xboole_0(X2) != iProver_top
% 3.67/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3804,plain,
% 3.67/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.67/0.98      | v1_xboole_0(X2) != iProver_top
% 3.67/0.98      | v1_xboole_0(k2_tarski(X0,X0)) = iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_1907,c_1905]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_8,plain,
% 3.67/0.98      ( ~ v1_xboole_0(k2_tarski(X0,X0)) ),
% 3.67/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_101,plain,
% 3.67/0.98      ( v1_xboole_0(k2_tarski(X0,X0)) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_5166,plain,
% 3.67/0.98      ( v1_xboole_0(X2) != iProver_top
% 3.67/0.98      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.67/0.98      inference(global_propositional_subsumption,
% 3.67/0.98                [status(thm)],
% 3.67/0.98                [c_3804,c_101]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_5167,plain,
% 3.67/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.67/0.98      | v1_xboole_0(X2) != iProver_top ),
% 3.67/0.98      inference(renaming,[status(thm)],[c_5166]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_5172,plain,
% 3.67/0.98      ( v1_xboole_0(X0) != iProver_top
% 3.67/0.98      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_1915,c_5167]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1894,plain,
% 3.67/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_10,plain,
% 3.67/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.67/0.98      | ~ r2_hidden(X2,X0)
% 3.67/0.98      | ~ v1_xboole_0(X1) ),
% 3.67/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1906,plain,
% 3.67/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.67/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.67/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3886,plain,
% 3.67/0.98      ( r2_hidden(X0,sK8) != iProver_top
% 3.67/0.98      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_1894,c_1906]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_5184,plain,
% 3.67/0.98      ( r2_hidden(X0,sK8) != iProver_top
% 3.67/0.98      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_5172,c_3886]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_5701,plain,
% 3.67/0.98      ( sK8 = sK6 | r2_hidden(X0,sK8) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_1876,c_5184]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_5889,plain,
% 3.67/0.98      ( sK8 = sK6 | r1_tarski(sK8,X0) = iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_1912,c_5701]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1888,plain,
% 3.67/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3888,plain,
% 3.67/0.98      ( r2_hidden(X0,sK6) != iProver_top
% 3.67/0.98      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_1888,c_1906]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_5183,plain,
% 3.67/0.98      ( r2_hidden(X0,sK6) != iProver_top
% 3.67/0.98      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_5172,c_3888]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_5545,plain,
% 3.67/0.98      ( sK8 = sK6 | r2_hidden(X0,sK6) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_1876,c_5183]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_5690,plain,
% 3.67/0.98      ( sK8 = sK6 | r1_tarski(sK6,X0) = iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_1912,c_5545]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_5,plain,
% 3.67/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.67/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1910,plain,
% 3.67/0.98      ( X0 = X1
% 3.67/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.67/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6027,plain,
% 3.67/0.98      ( sK8 = sK6 | sK6 = X0 | r1_tarski(X0,sK6) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_5690,c_1910]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6193,plain,
% 3.67/0.98      ( sK8 = sK6 ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_5889,c_6027]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_36,negated_conjecture,
% 3.67/0.98      ( m1_pre_topc(sK4,sK5) ),
% 3.67/0.98      inference(cnf_transformation,[],[f111]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1883,plain,
% 3.67/0.98      ( m1_pre_topc(sK4,sK5) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_17,plain,
% 3.67/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.67/0.98      | ~ m1_pre_topc(X3,X4)
% 3.67/0.98      | ~ m1_pre_topc(X3,X1)
% 3.67/0.98      | ~ m1_pre_topc(X1,X4)
% 3.67/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.67/0.98      | v2_struct_0(X4)
% 3.67/0.98      | v2_struct_0(X2)
% 3.67/0.98      | ~ v2_pre_topc(X2)
% 3.67/0.98      | ~ v2_pre_topc(X4)
% 3.67/0.98      | ~ l1_pre_topc(X2)
% 3.67/0.98      | ~ l1_pre_topc(X4)
% 3.67/0.98      | ~ v1_funct_1(X0)
% 3.67/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.67/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1901,plain,
% 3.67/0.98      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
% 3.67/0.98      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.67/0.98      | m1_pre_topc(X3,X4) != iProver_top
% 3.67/0.98      | m1_pre_topc(X0,X4) != iProver_top
% 3.67/0.98      | m1_pre_topc(X3,X0) != iProver_top
% 3.67/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.67/0.98      | v2_struct_0(X4) = iProver_top
% 3.67/0.98      | v2_struct_0(X1) = iProver_top
% 3.67/0.98      | v2_pre_topc(X1) != iProver_top
% 3.67/0.98      | v2_pre_topc(X4) != iProver_top
% 3.67/0.98      | l1_pre_topc(X1) != iProver_top
% 3.67/0.98      | l1_pre_topc(X4) != iProver_top
% 3.67/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_4386,plain,
% 3.67/0.98      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK5,X0,sK8)
% 3.67/0.98      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | m1_pre_topc(X0,X1) != iProver_top
% 3.67/0.98      | m1_pre_topc(X0,sK5) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK5,X1) != iProver_top
% 3.67/0.98      | v2_struct_0(X1) = iProver_top
% 3.67/0.98      | v2_struct_0(sK3) = iProver_top
% 3.67/0.98      | v2_pre_topc(X1) != iProver_top
% 3.67/0.98      | v2_pre_topc(sK3) != iProver_top
% 3.67/0.98      | l1_pre_topc(X1) != iProver_top
% 3.67/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.67/0.98      | v1_funct_1(sK8) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_1894,c_1901]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_60,plain,
% 3.67/0.98      ( v1_funct_1(sK8) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_61,plain,
% 3.67/0.98      ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_5116,plain,
% 3.67/0.98      ( v2_pre_topc(X1) != iProver_top
% 3.67/0.98      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK5,X0,sK8)
% 3.67/0.98      | m1_pre_topc(X0,X1) != iProver_top
% 3.67/0.98      | m1_pre_topc(X0,sK5) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK5,X1) != iProver_top
% 3.67/0.98      | v2_struct_0(X1) = iProver_top
% 3.67/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.67/0.98      inference(global_propositional_subsumption,
% 3.67/0.98                [status(thm)],
% 3.67/0.98                [c_4386,c_47,c_48,c_49,c_60,c_61]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_5117,plain,
% 3.67/0.98      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK5,X0,sK8)
% 3.67/0.98      | m1_pre_topc(X0,X1) != iProver_top
% 3.67/0.98      | m1_pre_topc(X0,sK5) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK5,X1) != iProver_top
% 3.67/0.98      | v2_struct_0(X1) = iProver_top
% 3.67/0.98      | v2_pre_topc(X1) != iProver_top
% 3.67/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.67/0.98      inference(renaming,[status(thm)],[c_5116]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_5123,plain,
% 3.67/0.98      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK8,u1_struct_0(sK4)) = k3_tmap_1(sK5,sK3,sK5,sK4,sK8)
% 3.67/0.98      | m1_pre_topc(sK5,sK5) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK4,sK5) != iProver_top
% 3.67/0.98      | v2_struct_0(sK5) = iProver_top
% 3.67/0.98      | v2_pre_topc(sK5) != iProver_top
% 3.67/0.98      | l1_pre_topc(sK5) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_1883,c_5117]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_16,plain,
% 3.67/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.67/0.98      | ~ m1_pre_topc(X3,X1)
% 3.67/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.67/0.98      | v2_struct_0(X1)
% 3.67/0.98      | v2_struct_0(X2)
% 3.67/0.98      | ~ v2_pre_topc(X2)
% 3.67/0.98      | ~ v2_pre_topc(X1)
% 3.67/0.98      | ~ l1_pre_topc(X2)
% 3.67/0.98      | ~ l1_pre_topc(X1)
% 3.67/0.98      | ~ v1_funct_1(X0)
% 3.67/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.67/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1902,plain,
% 3.67/0.98      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
% 3.67/0.98      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.67/0.98      | m1_pre_topc(X3,X0) != iProver_top
% 3.67/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.67/0.98      | v2_struct_0(X1) = iProver_top
% 3.67/0.98      | v2_struct_0(X0) = iProver_top
% 3.67/0.98      | v2_pre_topc(X1) != iProver_top
% 3.67/0.98      | v2_pre_topc(X0) != iProver_top
% 3.67/0.98      | l1_pre_topc(X1) != iProver_top
% 3.67/0.98      | l1_pre_topc(X0) != iProver_top
% 3.67/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_4315,plain,
% 3.67/0.98      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k2_tmap_1(sK5,sK3,sK8,X0)
% 3.67/0.98      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | m1_pre_topc(X0,sK5) != iProver_top
% 3.67/0.98      | v2_struct_0(sK5) = iProver_top
% 3.67/0.98      | v2_struct_0(sK3) = iProver_top
% 3.67/0.98      | v2_pre_topc(sK5) != iProver_top
% 3.67/0.98      | v2_pre_topc(sK3) != iProver_top
% 3.67/0.98      | l1_pre_topc(sK5) != iProver_top
% 3.67/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.67/0.98      | v1_funct_1(sK8) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_1894,c_1902]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_43,negated_conjecture,
% 3.67/0.98      ( ~ v2_struct_0(sK5) ),
% 3.67/0.98      inference(cnf_transformation,[],[f114]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_44,plain,
% 3.67/0.98      ( v2_struct_0(sK5) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_42,negated_conjecture,
% 3.67/0.98      ( v2_pre_topc(sK5) ),
% 3.67/0.98      inference(cnf_transformation,[],[f113]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_45,plain,
% 3.67/0.98      ( v2_pre_topc(sK5) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_41,negated_conjecture,
% 3.67/0.98      ( l1_pre_topc(sK5) ),
% 3.67/0.98      inference(cnf_transformation,[],[f112]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_46,plain,
% 3.67/0.98      ( l1_pre_topc(sK5) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_4725,plain,
% 3.67/0.98      ( m1_pre_topc(X0,sK5) != iProver_top
% 3.67/0.98      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k2_tmap_1(sK5,sK3,sK8,X0) ),
% 3.67/0.98      inference(global_propositional_subsumption,
% 3.67/0.98                [status(thm)],
% 3.67/0.98                [c_4315,c_44,c_45,c_46,c_47,c_48,c_49,c_60,c_61]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_4726,plain,
% 3.67/0.98      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK8,u1_struct_0(X0)) = k2_tmap_1(sK5,sK3,sK8,X0)
% 3.67/0.98      | m1_pre_topc(X0,sK5) != iProver_top ),
% 3.67/0.98      inference(renaming,[status(thm)],[c_4725]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_4732,plain,
% 3.67/0.98      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK8,u1_struct_0(sK4)) = k2_tmap_1(sK5,sK3,sK8,sK4) ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_1883,c_4726]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_5124,plain,
% 3.67/0.98      ( k3_tmap_1(sK5,sK3,sK5,sK4,sK8) = k2_tmap_1(sK5,sK3,sK8,sK4)
% 3.67/0.98      | m1_pre_topc(sK5,sK5) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK4,sK5) != iProver_top
% 3.67/0.98      | v2_struct_0(sK5) = iProver_top
% 3.67/0.98      | v2_pre_topc(sK5) != iProver_top
% 3.67/0.98      | l1_pre_topc(sK5) != iProver_top ),
% 3.67/0.98      inference(light_normalisation,[status(thm)],[c_5123,c_4732]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_51,plain,
% 3.67/0.98      ( m1_pre_topc(sK4,sK5) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_34,negated_conjecture,
% 3.67/0.98      ( m1_pre_topc(sK5,sK5) ),
% 3.67/0.98      inference(cnf_transformation,[],[f110]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_53,plain,
% 3.67/0.98      ( m1_pre_topc(sK5,sK5) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6520,plain,
% 3.67/0.98      ( k3_tmap_1(sK5,sK3,sK5,sK4,sK8) = k2_tmap_1(sK5,sK3,sK8,sK4) ),
% 3.67/0.98      inference(global_propositional_subsumption,
% 3.67/0.98                [status(thm)],
% 3.67/0.98                [c_5124,c_44,c_45,c_46,c_51,c_53]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6522,plain,
% 3.67/0.98      ( k3_tmap_1(sK5,sK3,sK5,sK4,sK6) = k2_tmap_1(sK5,sK3,sK6,sK4) ),
% 3.67/0.98      inference(light_normalisation,[status(thm)],[c_6520,c_6193]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6848,plain,
% 3.67/0.98      ( k2_tmap_1(sK5,sK3,sK6,sK4) = sK7
% 3.67/0.98      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) = iProver_top
% 3.67/0.98      | v1_funct_2(k2_tmap_1(sK5,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK5,sK5) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK4,sK5) != iProver_top
% 3.67/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.67/0.98      | v2_struct_0(sK5) = iProver_top
% 3.67/0.98      | v2_pre_topc(sK5) != iProver_top
% 3.67/0.98      | l1_pre_topc(sK5) != iProver_top
% 3.67/0.98      | v1_funct_1(k2_tmap_1(sK5,sK3,sK6,sK4)) != iProver_top
% 3.67/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.67/0.98      inference(light_normalisation,[status(thm)],[c_6844,c_6193,c_6522]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_54,plain,
% 3.67/0.98      ( v1_funct_1(sK6) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_55,plain,
% 3.67/0.98      ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_56,plain,
% 3.67/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_19,plain,
% 3.67/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.67/0.98      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 3.67/0.98      | ~ m1_pre_topc(X4,X3)
% 3.67/0.98      | ~ m1_pre_topc(X1,X3)
% 3.67/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.67/0.98      | v2_struct_0(X3)
% 3.67/0.98      | v2_struct_0(X2)
% 3.67/0.98      | ~ v2_pre_topc(X2)
% 3.67/0.98      | ~ v2_pre_topc(X3)
% 3.67/0.98      | ~ l1_pre_topc(X2)
% 3.67/0.98      | ~ l1_pre_topc(X3)
% 3.67/0.98      | ~ v1_funct_1(X0) ),
% 3.67/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1899,plain,
% 3.67/0.98      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.67/0.98      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2)) = iProver_top
% 3.67/0.98      | m1_pre_topc(X4,X3) != iProver_top
% 3.67/0.98      | m1_pre_topc(X1,X3) != iProver_top
% 3.67/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.67/0.98      | v2_struct_0(X2) = iProver_top
% 3.67/0.98      | v2_struct_0(X3) = iProver_top
% 3.67/0.98      | v2_pre_topc(X2) != iProver_top
% 3.67/0.98      | v2_pre_topc(X3) != iProver_top
% 3.67/0.98      | l1_pre_topc(X2) != iProver_top
% 3.67/0.98      | l1_pre_topc(X3) != iProver_top
% 3.67/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6524,plain,
% 3.67/0.98      ( v1_funct_2(k2_tmap_1(sK5,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top
% 3.67/0.98      | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK5,sK5) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK4,sK5) != iProver_top
% 3.67/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.67/0.98      | v2_struct_0(sK5) = iProver_top
% 3.67/0.98      | v2_struct_0(sK3) = iProver_top
% 3.67/0.98      | v2_pre_topc(sK5) != iProver_top
% 3.67/0.98      | v2_pre_topc(sK3) != iProver_top
% 3.67/0.98      | l1_pre_topc(sK5) != iProver_top
% 3.67/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.67/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_6522,c_1899]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_20,plain,
% 3.67/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.67/0.98      | ~ m1_pre_topc(X3,X4)
% 3.67/0.98      | ~ m1_pre_topc(X1,X4)
% 3.67/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.67/0.98      | v2_struct_0(X4)
% 3.67/0.98      | v2_struct_0(X2)
% 3.67/0.98      | ~ v2_pre_topc(X2)
% 3.67/0.98      | ~ v2_pre_topc(X4)
% 3.67/0.98      | ~ l1_pre_topc(X2)
% 3.67/0.98      | ~ l1_pre_topc(X4)
% 3.67/0.98      | ~ v1_funct_1(X0)
% 3.67/0.98      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 3.67/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1898,plain,
% 3.67/0.98      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.67/0.98      | m1_pre_topc(X3,X4) != iProver_top
% 3.67/0.98      | m1_pre_topc(X1,X4) != iProver_top
% 3.67/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.67/0.98      | v2_struct_0(X4) = iProver_top
% 3.67/0.98      | v2_struct_0(X2) = iProver_top
% 3.67/0.98      | v2_pre_topc(X2) != iProver_top
% 3.67/0.98      | v2_pre_topc(X4) != iProver_top
% 3.67/0.98      | l1_pre_topc(X2) != iProver_top
% 3.67/0.98      | l1_pre_topc(X4) != iProver_top
% 3.67/0.98      | v1_funct_1(X0) != iProver_top
% 3.67/0.98      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3685,plain,
% 3.67/0.98      ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | m1_pre_topc(X0,X1) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK5,X1) != iProver_top
% 3.67/0.98      | v2_struct_0(X1) = iProver_top
% 3.67/0.98      | v2_struct_0(sK3) = iProver_top
% 3.67/0.98      | v2_pre_topc(X1) != iProver_top
% 3.67/0.98      | v2_pre_topc(sK3) != iProver_top
% 3.67/0.98      | l1_pre_topc(X1) != iProver_top
% 3.67/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.67/0.98      | v1_funct_1(k3_tmap_1(X1,sK3,sK5,X0,sK6)) = iProver_top
% 3.67/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_1888,c_1898]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_5109,plain,
% 3.67/0.98      ( v1_funct_1(k3_tmap_1(X1,sK3,sK5,X0,sK6)) = iProver_top
% 3.67/0.98      | v2_pre_topc(X1) != iProver_top
% 3.67/0.98      | m1_pre_topc(X0,X1) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK5,X1) != iProver_top
% 3.67/0.98      | v2_struct_0(X1) = iProver_top
% 3.67/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.67/0.98      inference(global_propositional_subsumption,
% 3.67/0.98                [status(thm)],
% 3.67/0.98                [c_3685,c_47,c_48,c_49,c_54,c_55]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_5110,plain,
% 3.67/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK5,X1) != iProver_top
% 3.67/0.98      | v2_struct_0(X1) = iProver_top
% 3.67/0.98      | v2_pre_topc(X1) != iProver_top
% 3.67/0.98      | l1_pre_topc(X1) != iProver_top
% 3.67/0.98      | v1_funct_1(k3_tmap_1(X1,sK3,sK5,X0,sK6)) = iProver_top ),
% 3.67/0.98      inference(renaming,[status(thm)],[c_5109]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6525,plain,
% 3.67/0.98      ( m1_pre_topc(sK5,sK5) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK4,sK5) != iProver_top
% 3.67/0.98      | v2_struct_0(sK5) = iProver_top
% 3.67/0.98      | v2_pre_topc(sK5) != iProver_top
% 3.67/0.98      | l1_pre_topc(sK5) != iProver_top
% 3.67/0.98      | v1_funct_1(k2_tmap_1(sK5,sK3,sK6,sK4)) = iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_6522,c_5110]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6845,plain,
% 3.67/0.98      ( k3_tmap_1(sK5,sK3,sK5,sK4,sK6) = sK7
% 3.67/0.98      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) != iProver_top
% 3.67/0.98      | v1_funct_2(k3_tmap_1(sK5,sK3,sK5,sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK5,sK5) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK4,sK5) != iProver_top
% 3.67/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.67/0.98      | v2_struct_0(sK5) = iProver_top
% 3.67/0.98      | v2_pre_topc(sK5) != iProver_top
% 3.67/0.98      | l1_pre_topc(sK5) != iProver_top
% 3.67/0.98      | v1_funct_1(k3_tmap_1(sK5,sK3,sK5,sK4,sK6)) != iProver_top
% 3.67/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_6522,c_6841]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6846,plain,
% 3.67/0.98      ( k3_tmap_1(sK5,sK3,sK5,sK4,sK6) = sK7
% 3.67/0.98      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) != iProver_top
% 3.67/0.98      | v1_funct_2(k2_tmap_1(sK5,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK5,sK5) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK4,sK5) != iProver_top
% 3.67/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.67/0.98      | v2_struct_0(sK5) = iProver_top
% 3.67/0.98      | v2_pre_topc(sK5) != iProver_top
% 3.67/0.98      | l1_pre_topc(sK5) != iProver_top
% 3.67/0.98      | v1_funct_1(k2_tmap_1(sK5,sK3,sK6,sK4)) != iProver_top
% 3.67/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.67/0.98      inference(light_normalisation,[status(thm)],[c_6845,c_6522]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6847,plain,
% 3.67/0.98      ( k2_tmap_1(sK5,sK3,sK6,sK4) = sK7
% 3.67/0.98      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) != iProver_top
% 3.67/0.98      | v1_funct_2(k2_tmap_1(sK5,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK5,sK5) != iProver_top
% 3.67/0.98      | m1_pre_topc(sK4,sK5) != iProver_top
% 3.67/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.67/0.98      | v2_struct_0(sK5) = iProver_top
% 3.67/0.98      | v2_pre_topc(sK5) != iProver_top
% 3.67/0.98      | l1_pre_topc(sK5) != iProver_top
% 3.67/0.98      | v1_funct_1(k2_tmap_1(sK5,sK3,sK6,sK4)) != iProver_top
% 3.67/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.67/0.98      inference(demodulation,[status(thm)],[c_6846,c_6522]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6852,plain,
% 3.67/0.98      ( k2_tmap_1(sK5,sK3,sK6,sK4) = sK7 ),
% 3.67/0.98      inference(global_propositional_subsumption,
% 3.67/0.98                [status(thm)],
% 3.67/0.98                [c_6848,c_44,c_45,c_46,c_47,c_48,c_49,c_51,c_53,c_54,
% 3.67/0.98                 c_55,c_56,c_6524,c_6525,c_6847]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6855,plain,
% 3.67/0.98      ( k3_tmap_1(sK5,sK3,sK5,sK4,sK6) = sK7 ),
% 3.67/0.98      inference(demodulation,[status(thm)],[c_6852,c_6522]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_22,negated_conjecture,
% 3.67/0.98      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK5,sK3,sK5,sK4,sK8),sK7)
% 3.67/0.98      | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) ),
% 3.67/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1896,plain,
% 3.67/0.98      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK5,sK3,sK5,sK4,sK8),sK7) != iProver_top
% 3.67/0.98      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK5,sK3,sK6,sK4),sK7) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6858,plain,
% 3.67/0.98      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK5,sK3,sK5,sK4,sK8),sK7) != iProver_top
% 3.67/0.98      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK7,sK7) != iProver_top ),
% 3.67/0.98      inference(demodulation,[status(thm)],[c_6852,c_1896]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6859,plain,
% 3.67/0.98      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK5,sK3,sK5,sK4,sK6),sK7) != iProver_top
% 3.67/0.98      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK7,sK7) != iProver_top ),
% 3.67/0.98      inference(light_normalisation,[status(thm)],[c_6858,c_6193]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_6860,plain,
% 3.67/0.98      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK7,sK7) != iProver_top ),
% 3.67/0.98      inference(demodulation,[status(thm)],[c_6855,c_6859]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_12,plain,
% 3.67/0.98      ( r2_funct_2(X0,X1,X2,X2)
% 3.67/0.98      | ~ v1_funct_2(X2,X0,X1)
% 3.67/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.67/0.98      | ~ v1_funct_1(X2) ),
% 3.67/0.98      inference(cnf_transformation,[],[f117]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_1904,plain,
% 3.67/0.98      ( r2_funct_2(X0,X1,X2,X2) = iProver_top
% 3.67/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.67/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.67/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3901,plain,
% 3.67/0.98      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK7,sK7) = iProver_top
% 3.67/0.98      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.67/0.98      | v1_funct_1(sK7) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_1891,c_1904]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(contradiction,plain,
% 3.67/0.98      ( $false ),
% 3.67/0.98      inference(minisat,[status(thm)],[c_6860,c_3901,c_58,c_57]) ).
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.67/0.98  
% 3.67/0.98  ------                               Statistics
% 3.67/0.98  
% 3.67/0.98  ------ General
% 3.67/0.98  
% 3.67/0.98  abstr_ref_over_cycles:                  0
% 3.67/0.98  abstr_ref_under_cycles:                 0
% 3.67/0.98  gc_basic_clause_elim:                   0
% 3.67/0.98  forced_gc_time:                         0
% 3.67/0.98  parsing_time:                           0.011
% 3.67/0.98  unif_index_cands_time:                  0.
% 3.67/0.98  unif_index_add_time:                    0.
% 3.67/0.98  orderings_time:                         0.
% 3.67/0.98  out_proof_time:                         0.017
% 3.67/0.98  total_time:                             0.322
% 3.67/0.98  num_of_symbols:                         58
% 3.67/0.98  num_of_terms:                           8817
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing
% 3.67/0.98  
% 3.67/0.98  num_of_splits:                          0
% 3.67/0.98  num_of_split_atoms:                     0
% 3.67/0.98  num_of_reused_defs:                     0
% 3.67/0.98  num_eq_ax_congr_red:                    27
% 3.67/0.98  num_of_sem_filtered_clauses:            1
% 3.67/0.98  num_of_subtypes:                        0
% 3.67/0.98  monotx_restored_types:                  0
% 3.67/0.98  sat_num_of_epr_types:                   0
% 3.67/0.98  sat_num_of_non_cyclic_types:            0
% 3.67/0.98  sat_guarded_non_collapsed_types:        0
% 3.67/0.98  num_pure_diseq_elim:                    0
% 3.67/0.98  simp_replaced_by:                       0
% 3.67/0.98  res_preprocessed:                       199
% 3.67/0.98  prep_upred:                             0
% 3.67/0.98  prep_unflattend:                        12
% 3.67/0.98  smt_new_axioms:                         0
% 3.67/0.98  pred_elim_cands:                        11
% 3.67/0.98  pred_elim:                              1
% 3.67/0.98  pred_elim_cl:                           2
% 3.67/0.98  pred_elim_cycles:                       3
% 3.67/0.98  merged_defs:                            8
% 3.67/0.98  merged_defs_ncl:                        0
% 3.67/0.98  bin_hyper_res:                          8
% 3.67/0.98  prep_cycles:                            4
% 3.67/0.98  pred_elim_time:                         0.003
% 3.67/0.98  splitting_time:                         0.
% 3.67/0.98  sem_filter_time:                        0.
% 3.67/0.98  monotx_time:                            0.001
% 3.67/0.98  subtype_inf_time:                       0.
% 3.67/0.98  
% 3.67/0.98  ------ Problem properties
% 3.67/0.98  
% 3.67/0.98  clauses:                                40
% 3.67/0.98  conjectures:                            20
% 3.67/0.98  epr:                                    17
% 3.67/0.98  horn:                                   31
% 3.67/0.98  ground:                                 21
% 3.67/0.98  unary:                                  20
% 3.67/0.98  binary:                                 8
% 3.67/0.98  lits:                                   125
% 3.67/0.98  lits_eq:                                5
% 3.67/0.98  fd_pure:                                0
% 3.67/0.98  fd_pseudo:                              0
% 3.67/0.98  fd_cond:                                0
% 3.67/0.98  fd_pseudo_cond:                         2
% 3.67/0.98  ac_symbols:                             0
% 3.67/0.98  
% 3.67/0.98  ------ Propositional Solver
% 3.67/0.98  
% 3.67/0.98  prop_solver_calls:                      30
% 3.67/0.98  prop_fast_solver_calls:                 1871
% 3.67/0.98  smt_solver_calls:                       0
% 3.67/0.98  smt_fast_solver_calls:                  0
% 3.67/0.98  prop_num_of_clauses:                    3120
% 3.67/0.98  prop_preprocess_simplified:             9274
% 3.67/0.98  prop_fo_subsumed:                       120
% 3.67/0.98  prop_solver_time:                       0.
% 3.67/0.98  smt_solver_time:                        0.
% 3.67/0.98  smt_fast_solver_time:                   0.
% 3.67/0.98  prop_fast_solver_time:                  0.
% 3.67/0.98  prop_unsat_core_time:                   0.
% 3.67/0.98  
% 3.67/0.98  ------ QBF
% 3.67/0.98  
% 3.67/0.98  qbf_q_res:                              0
% 3.67/0.98  qbf_num_tautologies:                    0
% 3.67/0.98  qbf_prep_cycles:                        0
% 3.67/0.98  
% 3.67/0.98  ------ BMC1
% 3.67/0.98  
% 3.67/0.98  bmc1_current_bound:                     -1
% 3.67/0.98  bmc1_last_solved_bound:                 -1
% 3.67/0.98  bmc1_unsat_core_size:                   -1
% 3.67/0.98  bmc1_unsat_core_parents_size:           -1
% 3.67/0.98  bmc1_merge_next_fun:                    0
% 3.67/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.67/0.98  
% 3.67/0.98  ------ Instantiation
% 3.67/0.98  
% 3.67/0.98  inst_num_of_clauses:                    813
% 3.67/0.98  inst_num_in_passive:                    312
% 3.67/0.98  inst_num_in_active:                     469
% 3.67/0.98  inst_num_in_unprocessed:                33
% 3.67/0.98  inst_num_of_loops:                      510
% 3.67/0.98  inst_num_of_learning_restarts:          0
% 3.67/0.98  inst_num_moves_active_passive:          38
% 3.67/0.98  inst_lit_activity:                      0
% 3.67/0.98  inst_lit_activity_moves:                0
% 3.67/0.98  inst_num_tautologies:                   0
% 3.67/0.98  inst_num_prop_implied:                  0
% 3.67/0.98  inst_num_existing_simplified:           0
% 3.67/0.98  inst_num_eq_res_simplified:             0
% 3.67/0.98  inst_num_child_elim:                    0
% 3.67/0.98  inst_num_of_dismatching_blockings:      32
% 3.67/0.98  inst_num_of_non_proper_insts:           750
% 3.67/0.98  inst_num_of_duplicates:                 0
% 3.67/0.98  inst_inst_num_from_inst_to_res:         0
% 3.67/0.98  inst_dismatching_checking_time:         0.
% 3.67/0.98  
% 3.67/0.98  ------ Resolution
% 3.67/0.98  
% 3.67/0.98  res_num_of_clauses:                     0
% 3.67/0.98  res_num_in_passive:                     0
% 3.67/0.98  res_num_in_active:                      0
% 3.67/0.98  res_num_of_loops:                       203
% 3.67/0.98  res_forward_subset_subsumed:            30
% 3.67/0.98  res_backward_subset_subsumed:           2
% 3.67/0.98  res_forward_subsumed:                   0
% 3.67/0.98  res_backward_subsumed:                  0
% 3.67/0.98  res_forward_subsumption_resolution:     0
% 3.67/0.98  res_backward_subsumption_resolution:    0
% 3.67/0.98  res_clause_to_clause_subsumption:       291
% 3.67/0.98  res_orphan_elimination:                 0
% 3.67/0.98  res_tautology_del:                      29
% 3.67/0.98  res_num_eq_res_simplified:              0
% 3.67/0.98  res_num_sel_changes:                    0
% 3.67/0.98  res_moves_from_active_to_pass:          0
% 3.67/0.98  
% 3.67/0.98  ------ Superposition
% 3.67/0.98  
% 3.67/0.98  sup_time_total:                         0.
% 3.67/0.98  sup_time_generating:                    0.
% 3.67/0.98  sup_time_sim_full:                      0.
% 3.67/0.98  sup_time_sim_immed:                     0.
% 3.67/0.98  
% 3.67/0.98  sup_num_of_clauses:                     120
% 3.67/0.98  sup_num_in_active:                      88
% 3.67/0.98  sup_num_in_passive:                     32
% 3.67/0.98  sup_num_of_loops:                       101
% 3.67/0.98  sup_fw_superposition:                   98
% 3.67/0.98  sup_bw_superposition:                   34
% 3.67/0.98  sup_immediate_simplified:               20
% 3.67/0.98  sup_given_eliminated:                   0
% 3.67/0.98  comparisons_done:                       0
% 3.67/0.98  comparisons_avoided:                    0
% 3.67/0.98  
% 3.67/0.98  ------ Simplifications
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  sim_fw_subset_subsumed:                 2
% 3.67/0.98  sim_bw_subset_subsumed:                 22
% 3.67/0.98  sim_fw_subsumed:                        7
% 3.67/0.98  sim_bw_subsumed:                        0
% 3.67/0.98  sim_fw_subsumption_res:                 0
% 3.67/0.98  sim_bw_subsumption_res:                 0
% 3.67/0.98  sim_tautology_del:                      6
% 3.67/0.98  sim_eq_tautology_del:                   9
% 3.67/0.98  sim_eq_res_simp:                        0
% 3.67/0.98  sim_fw_demodulated:                     2
% 3.67/0.98  sim_bw_demodulated:                     7
% 3.67/0.98  sim_light_normalised:                   12
% 3.67/0.98  sim_joinable_taut:                      0
% 3.67/0.98  sim_joinable_simp:                      0
% 3.67/0.98  sim_ac_normalised:                      0
% 3.67/0.98  sim_smt_subsumption:                    0
% 3.67/0.98  
%------------------------------------------------------------------------------
