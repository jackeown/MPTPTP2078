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
% DateTime   : Thu Dec  3 12:23:01 EST 2020

% Result     : Theorem 6.54s
% Output     : CNFRefutation 6.54s
% Verified   : 
% Statistics : Number of formulae       :  258 (18779 expanded)
%              Number of clauses        :  159 (2821 expanded)
%              Number of leaves         :   24 (8156 expanded)
%              Depth                    :   31
%              Number of atoms          : 1581 (411795 expanded)
%              Number of equality atoms :  354 (24270 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   50 (   5 average)
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
    inference(negated_conjecture,[],[f17])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f60,plain,(
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

fof(f59,plain,(
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

fof(f58,plain,(
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

fof(f57,plain,(
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

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f61,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f53,f60,f59,f58,f57,f56,f55,f54])).

fof(f95,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f105,plain,(
    sK0 = sK3 ),
    inference(cnf_transformation,[],[f61])).

fof(f104,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f61])).

fof(f11,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f106,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f89,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f91,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f96,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f97,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

fof(f98,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f61])).

fof(f102,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f103,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f87,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f88,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f90,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f93,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f15,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f92,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f13,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
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

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f30])).

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
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f82,plain,(
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

fof(f81,plain,(
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

fof(f83,plain,(
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

fof(f107,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f108,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_37,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_994,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_2001,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_994])).

cnf(c_27,negated_conjecture,
    ( sK0 = sK3 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1004,negated_conjecture,
    ( sK0 = sK3 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_2029,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2001,c_1004])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1003,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1992,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1003])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f75])).

cnf(c_26,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_636,plain,
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
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_637,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK4)
    | sK6 = sK4 ),
    inference(unflattening,[status(thm)],[c_636])).

cnf(c_43,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_41,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_101,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_105,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_639,plain,
    ( sK6 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_637,c_43,c_41,c_36,c_35,c_34,c_30,c_29,c_28,c_101,c_105])).

cnf(c_983,plain,
    ( sK6 = sK4 ),
    inference(subtyping,[status(esa)],[c_639])).

cnf(c_2050,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1992,c_983,c_1004])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f77])).

cnf(c_1015,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61))
    | ~ m1_pre_topc(X2_61,X0_61)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
    | ~ v2_pre_topc(X1_61)
    | ~ v2_pre_topc(X0_61)
    | v2_struct_0(X1_61)
    | v2_struct_0(X0_61)
    | ~ l1_pre_topc(X1_61)
    | ~ l1_pre_topc(X0_61)
    | ~ v1_funct_1(X0_57)
    | k2_partfun1(u1_struct_0(X0_61),u1_struct_0(X1_61),X0_57,u1_struct_0(X2_61)) = k2_tmap_1(X0_61,X1_61,X0_57,X2_61) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1981,plain,
    ( k2_partfun1(u1_struct_0(X0_61),u1_struct_0(X1_61),X0_57,u1_struct_0(X2_61)) = k2_tmap_1(X0_61,X1_61,X0_57,X2_61)
    | v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61)) != iProver_top
    | m1_pre_topc(X2_61,X0_61) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61)))) != iProver_top
    | v2_pre_topc(X1_61) != iProver_top
    | v2_pre_topc(X0_61) != iProver_top
    | v2_struct_0(X1_61) = iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | l1_pre_topc(X1_61) != iProver_top
    | l1_pre_topc(X0_61) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1015])).

cnf(c_4686,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_61)) = k2_tmap_1(sK0,sK1,sK4,X0_61)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_61,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2050,c_1981])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1020,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
    | ~ v1_funct_1(X0_57)
    | k2_partfun1(X0_60,X1_60,X0_57,X2_60) = k7_relat_1(X0_57,X2_60) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1976,plain,
    ( k2_partfun1(X0_60,X1_60,X0_57,X2_60) = k7_relat_1(X0_57,X2_60)
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_3099,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_60) = k7_relat_1(sK4,X0_60)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2050,c_1976])).

cnf(c_2456,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_60) = k7_relat_1(sK4,X0_60) ),
    inference(instantiation,[status(thm)],[c_1020])).

cnf(c_3759,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_60) = k7_relat_1(sK4,X0_60) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3099,c_36,c_34,c_2456])).

cnf(c_4755,plain,
    ( k2_tmap_1(sK0,sK1,sK4,X0_61) = k7_relat_1(sK4,u1_struct_0(X0_61))
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_61,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4686,c_3759])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_47,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_48,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_49,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_50,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_51,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_52,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_57,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_58,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6820,plain,
    ( m1_pre_topc(X0_61,sK0) != iProver_top
    | k2_tmap_1(sK0,sK1,sK4,X0_61) = k7_relat_1(sK4,u1_struct_0(X0_61)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4755,c_47,c_48,c_49,c_50,c_51,c_52,c_57,c_58])).

cnf(c_6821,plain,
    ( k2_tmap_1(sK0,sK1,sK4,X0_61) = k7_relat_1(sK4,u1_struct_0(X0_61))
    | m1_pre_topc(X0_61,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6820])).

cnf(c_6829,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK0) = k7_relat_1(sK4,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_2029,c_6821])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_593,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_4,c_1])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_597,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_593,c_3])).

cnf(c_598,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_597])).

cnf(c_2,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_598,c_2])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_614,c_3])).

cnf(c_984,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
    | k7_relat_1(X0_57,X0_60) = X0_57 ),
    inference(subtyping,[status(esa)],[c_618])).

cnf(c_2011,plain,
    ( k7_relat_1(X0_57,X0_60) = X0_57
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_984])).

cnf(c_6362,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK0)) = sK4 ),
    inference(superposition,[status(thm)],[c_2050,c_2011])).

cnf(c_6831,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK0) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_6829,c_6362])).

cnf(c_39,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_992,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_39])).

cnf(c_2003,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_992])).

cnf(c_6828,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_2003,c_6821])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f84])).

cnf(c_1008,plain,
    ( r2_funct_2(u1_struct_0(X0_61),u1_struct_0(X1_61),k3_tmap_1(X2_61,X1_61,X3_61,X0_61,k2_tmap_1(X2_61,X1_61,X0_57,X3_61)),k2_tmap_1(X2_61,X1_61,X0_57,X0_61))
    | ~ v1_funct_2(X0_57,u1_struct_0(X2_61),u1_struct_0(X1_61))
    | ~ m1_pre_topc(X3_61,X2_61)
    | ~ m1_pre_topc(X0_61,X2_61)
    | ~ m1_pre_topc(X0_61,X3_61)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_61),u1_struct_0(X1_61))))
    | ~ v2_pre_topc(X1_61)
    | ~ v2_pre_topc(X2_61)
    | v2_struct_0(X2_61)
    | v2_struct_0(X1_61)
    | v2_struct_0(X0_61)
    | v2_struct_0(X3_61)
    | ~ l1_pre_topc(X1_61)
    | ~ l1_pre_topc(X2_61)
    | ~ v1_funct_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1988,plain,
    ( r2_funct_2(u1_struct_0(X0_61),u1_struct_0(X1_61),k3_tmap_1(X2_61,X1_61,X3_61,X0_61,k2_tmap_1(X2_61,X1_61,X0_57,X3_61)),k2_tmap_1(X2_61,X1_61,X0_57,X0_61)) = iProver_top
    | v1_funct_2(X0_57,u1_struct_0(X2_61),u1_struct_0(X1_61)) != iProver_top
    | m1_pre_topc(X3_61,X2_61) != iProver_top
    | m1_pre_topc(X0_61,X2_61) != iProver_top
    | m1_pre_topc(X0_61,X3_61) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_61),u1_struct_0(X1_61)))) != iProver_top
    | v2_pre_topc(X1_61) != iProver_top
    | v2_pre_topc(X2_61) != iProver_top
    | v2_struct_0(X2_61) = iProver_top
    | v2_struct_0(X1_61) = iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | v2_struct_0(X3_61) = iProver_top
    | l1_pre_topc(X1_61) != iProver_top
    | l1_pre_topc(X2_61) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1008])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1007,plain,
    ( ~ m1_pre_topc(X0_61,X1_61)
    | ~ m1_pre_topc(X2_61,X0_61)
    | m1_pre_topc(X2_61,X1_61)
    | ~ v2_pre_topc(X1_61)
    | ~ l1_pre_topc(X1_61) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1989,plain,
    ( m1_pre_topc(X0_61,X1_61) != iProver_top
    | m1_pre_topc(X2_61,X0_61) != iProver_top
    | m1_pre_topc(X2_61,X1_61) = iProver_top
    | v2_pre_topc(X1_61) != iProver_top
    | l1_pre_topc(X1_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1007])).

cnf(c_2278,plain,
    ( r2_funct_2(u1_struct_0(X0_61),u1_struct_0(X1_61),k3_tmap_1(X2_61,X1_61,X3_61,X0_61,k2_tmap_1(X2_61,X1_61,X0_57,X3_61)),k2_tmap_1(X2_61,X1_61,X0_57,X0_61)) = iProver_top
    | v1_funct_2(X0_57,u1_struct_0(X2_61),u1_struct_0(X1_61)) != iProver_top
    | m1_pre_topc(X3_61,X2_61) != iProver_top
    | m1_pre_topc(X0_61,X3_61) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_61),u1_struct_0(X1_61)))) != iProver_top
    | v2_pre_topc(X1_61) != iProver_top
    | v2_pre_topc(X2_61) != iProver_top
    | v2_struct_0(X2_61) = iProver_top
    | v2_struct_0(X1_61) = iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | v2_struct_0(X3_61) = iProver_top
    | l1_pre_topc(X1_61) != iProver_top
    | l1_pre_topc(X2_61) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1988,c_1989])).

cnf(c_6999,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_61,sK2,k2_tmap_1(sK0,sK1,sK4,X0_61)),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_61,sK0) != iProver_top
    | m1_pre_topc(sK2,X0_61) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6828,c_2278])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_53,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_59,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_8681,plain,
    ( m1_pre_topc(sK2,X0_61) != iProver_top
    | m1_pre_topc(X0_61,sK0) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_61,sK2,k2_tmap_1(sK0,sK1,sK4,X0_61)),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6999,c_47,c_48,c_49,c_50,c_51,c_52,c_53,c_57,c_58,c_59])).

cnf(c_8682,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_61,sK2,k2_tmap_1(sK0,sK1,sK4,X0_61)),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
    | m1_pre_topc(X0_61,sK0) != iProver_top
    | m1_pre_topc(sK2,X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(renaming,[status(thm)],[c_8681])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1014,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
    | m1_subset_1(k2_tmap_1(X0_61,X1_61,X0_57,X2_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_61),u1_struct_0(X1_61))))
    | ~ l1_struct_0(X1_61)
    | ~ l1_struct_0(X2_61)
    | ~ l1_struct_0(X0_61)
    | ~ v1_funct_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1982,plain,
    ( v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_61,X1_61,X0_57,X2_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_61),u1_struct_0(X1_61)))) = iProver_top
    | l1_struct_0(X1_61) != iProver_top
    | l1_struct_0(X2_61) != iProver_top
    | l1_struct_0(X0_61) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1014])).

cnf(c_6855,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6828,c_1982])).

cnf(c_104,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_106,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_104])).

cnf(c_1017,plain,
    ( ~ l1_pre_topc(X0_61)
    | l1_struct_0(X0_61) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2750,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1017])).

cnf(c_2751,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2750])).

cnf(c_2753,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1017])).

cnf(c_2754,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2753])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1016,plain,
    ( ~ m1_pre_topc(X0_61,X1_61)
    | ~ l1_pre_topc(X1_61)
    | l1_pre_topc(X0_61) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1980,plain,
    ( m1_pre_topc(X0_61,X1_61) != iProver_top
    | l1_pre_topc(X1_61) != iProver_top
    | l1_pre_topc(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_3087,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2003,c_1980])).

cnf(c_7757,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6855,c_49,c_52,c_57,c_58,c_59,c_106,c_2751,c_2754,c_3087])).

cnf(c_9,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1018,plain,
    ( ~ r2_funct_2(X0_60,X1_60,X0_57,X1_57)
    | ~ v1_funct_2(X1_57,X0_60,X1_60)
    | ~ v1_funct_2(X0_57,X0_60,X1_60)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
    | ~ v1_funct_1(X0_57)
    | ~ v1_funct_1(X1_57)
    | X1_57 = X0_57 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1978,plain,
    ( X0_57 = X1_57
    | r2_funct_2(X0_60,X1_60,X1_57,X0_57) != iProver_top
    | v1_funct_2(X1_57,X0_60,X1_60) != iProver_top
    | v1_funct_2(X0_57,X0_60,X1_60) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1018])).

cnf(c_7764,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_57
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_57,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7757,c_1978])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1013,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61))
    | v1_funct_2(k2_tmap_1(X0_61,X1_61,X0_57,X2_61),u1_struct_0(X2_61),u1_struct_0(X1_61))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
    | ~ l1_struct_0(X1_61)
    | ~ l1_struct_0(X2_61)
    | ~ l1_struct_0(X0_61)
    | ~ v1_funct_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1983,plain,
    ( v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_61,X1_61,X0_57,X2_61),u1_struct_0(X2_61),u1_struct_0(X1_61)) = iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61)))) != iProver_top
    | l1_struct_0(X1_61) != iProver_top
    | l1_struct_0(X2_61) != iProver_top
    | l1_struct_0(X0_61) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1013])).

cnf(c_6856,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6828,c_1983])).

cnf(c_11945,plain,
    ( v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_57,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
    | k7_relat_1(sK4,u1_struct_0(sK2)) = X0_57
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7764,c_49,c_52,c_57,c_58,c_59,c_106,c_2751,c_2754,c_3087,c_6856])).

cnf(c_11946,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_57
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_57,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11945])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1021,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
    | ~ v1_funct_1(X0_57)
    | v1_funct_1(k2_partfun1(X0_60,X1_60,X0_57,X2_60)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1975,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(k2_partfun1(X0_60,X1_60,X0_57,X2_60)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1021])).

cnf(c_2957,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_60)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2050,c_1975])).

cnf(c_2416,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_60))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1021])).

cnf(c_2417,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_60)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2416])).

cnf(c_3611,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_60)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2957,c_57,c_59,c_2417])).

cnf(c_3763,plain,
    ( v1_funct_1(k7_relat_1(sK4,X0_60)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3759,c_3611])).

cnf(c_11957,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_57
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_57,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11946,c_3763])).

cnf(c_11961,plain,
    ( k3_tmap_1(sK0,sK1,X0_61,sK2,k2_tmap_1(sK0,sK1,sK4,X0_61)) = k7_relat_1(sK4,u1_struct_0(sK2))
    | v1_funct_2(k3_tmap_1(sK0,sK1,X0_61,sK2,k2_tmap_1(sK0,sK1,sK4,X0_61)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_61,sK0) != iProver_top
    | m1_pre_topc(sK2,X0_61) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,X0_61,sK2,k2_tmap_1(sK0,sK1,sK4,X0_61)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,X0_61,sK2,k2_tmap_1(sK0,sK1,sK4,X0_61))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8682,c_11957])).

cnf(c_14721,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0)) = k7_relat_1(sK4,u1_struct_0(sK2))
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6831,c_11961])).

cnf(c_14729,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14721,c_6831])).

cnf(c_54,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f82])).

cnf(c_1010,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61))
    | v1_funct_2(k3_tmap_1(X2_61,X1_61,X0_61,X3_61,X0_57),u1_struct_0(X3_61),u1_struct_0(X1_61))
    | ~ m1_pre_topc(X3_61,X2_61)
    | ~ m1_pre_topc(X0_61,X2_61)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
    | ~ v2_pre_topc(X1_61)
    | ~ v2_pre_topc(X2_61)
    | v2_struct_0(X2_61)
    | v2_struct_0(X1_61)
    | ~ l1_pre_topc(X1_61)
    | ~ l1_pre_topc(X2_61)
    | ~ v1_funct_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2581,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61))
    | v1_funct_2(k3_tmap_1(sK0,X1_61,X0_61,sK2,X0_57),u1_struct_0(sK2),u1_struct_0(X1_61))
    | ~ m1_pre_topc(X0_61,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
    | ~ v2_pre_topc(X1_61)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X1_61)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X1_61)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_57) ),
    inference(instantiation,[status(thm)],[c_1010])).

cnf(c_3205,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(sK0),u1_struct_0(X0_61))
    | v1_funct_2(k3_tmap_1(sK0,X0_61,sK0,sK2,X0_57),u1_struct_0(sK2),u1_struct_0(X0_61))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_61))))
    | ~ v2_pre_topc(X0_61)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0_61)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X0_61)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_57) ),
    inference(instantiation,[status(thm)],[c_2581])).

cnf(c_4493,plain,
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
    inference(instantiation,[status(thm)],[c_3205])).

cnf(c_4494,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4493])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_1009,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61))
    | ~ m1_pre_topc(X0_61,X2_61)
    | ~ m1_pre_topc(X3_61,X2_61)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
    | ~ v2_pre_topc(X1_61)
    | ~ v2_pre_topc(X2_61)
    | v2_struct_0(X1_61)
    | v2_struct_0(X2_61)
    | ~ l1_pre_topc(X1_61)
    | ~ l1_pre_topc(X2_61)
    | ~ v1_funct_1(X0_57)
    | v1_funct_1(k3_tmap_1(X2_61,X1_61,X0_61,X3_61,X0_57)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_3183,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(sK0),u1_struct_0(X0_61))
    | ~ m1_pre_topc(X1_61,X2_61)
    | ~ m1_pre_topc(sK0,X2_61)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_61))))
    | ~ v2_pre_topc(X2_61)
    | ~ v2_pre_topc(X0_61)
    | v2_struct_0(X2_61)
    | v2_struct_0(X0_61)
    | ~ l1_pre_topc(X2_61)
    | ~ l1_pre_topc(X0_61)
    | ~ v1_funct_1(X0_57)
    | v1_funct_1(k3_tmap_1(X2_61,X0_61,sK0,X1_61,X0_57)) ),
    inference(instantiation,[status(thm)],[c_1009])).

cnf(c_5037,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(sK0),u1_struct_0(X0_61))
    | ~ m1_pre_topc(X1_61,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_61))))
    | ~ v2_pre_topc(X0_61)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0_61)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X0_61)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_57)
    | v1_funct_1(k3_tmap_1(sK0,X0_61,sK0,X1_61,X0_57)) ),
    inference(instantiation,[status(thm)],[c_3183])).

cnf(c_9162,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(sK0),u1_struct_0(X0_61))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_61))))
    | ~ v2_pre_topc(X0_61)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0_61)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X0_61)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_57)
    | v1_funct_1(k3_tmap_1(sK0,X0_61,sK0,sK2,X0_57)) ),
    inference(instantiation,[status(thm)],[c_5037])).

cnf(c_11166,plain,
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
    inference(instantiation,[status(thm)],[c_9162])).

cnf(c_11167,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_11166])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f83])).

cnf(c_1011,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61))
    | ~ m1_pre_topc(X0_61,X2_61)
    | ~ m1_pre_topc(X3_61,X2_61)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
    | m1_subset_1(k3_tmap_1(X2_61,X1_61,X0_61,X3_61,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_61),u1_struct_0(X1_61))))
    | ~ v2_pre_topc(X1_61)
    | ~ v2_pre_topc(X2_61)
    | v2_struct_0(X1_61)
    | v2_struct_0(X2_61)
    | ~ l1_pre_topc(X1_61)
    | ~ l1_pre_topc(X2_61)
    | ~ v1_funct_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3182,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(sK0),u1_struct_0(X0_61))
    | ~ m1_pre_topc(X1_61,X2_61)
    | ~ m1_pre_topc(sK0,X2_61)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_61))))
    | m1_subset_1(k3_tmap_1(X2_61,X0_61,sK0,X1_61,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_61),u1_struct_0(X0_61))))
    | ~ v2_pre_topc(X2_61)
    | ~ v2_pre_topc(X0_61)
    | v2_struct_0(X2_61)
    | v2_struct_0(X0_61)
    | ~ l1_pre_topc(X2_61)
    | ~ l1_pre_topc(X0_61)
    | ~ v1_funct_1(X0_57) ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_5057,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(sK0),u1_struct_0(X0_61))
    | ~ m1_pre_topc(X1_61,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_61))))
    | m1_subset_1(k3_tmap_1(sK0,X0_61,sK0,X1_61,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_61),u1_struct_0(X0_61))))
    | ~ v2_pre_topc(X0_61)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0_61)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X0_61)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_57) ),
    inference(instantiation,[status(thm)],[c_3182])).

cnf(c_9442,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(sK0),u1_struct_0(X0_61))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_61))))
    | m1_subset_1(k3_tmap_1(sK0,X0_61,sK0,sK2,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_61))))
    | ~ v2_pre_topc(X0_61)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0_61)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X0_61)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_57) ),
    inference(instantiation,[status(thm)],[c_5057])).

cnf(c_11392,plain,
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
    inference(instantiation,[status(thm)],[c_9442])).

cnf(c_11393,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_11392])).

cnf(c_8692,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6831,c_8682])).

cnf(c_12988,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8692,c_47,c_54,c_2029])).

cnf(c_12994,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12988,c_11957])).

cnf(c_14896,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14729,c_47,c_48,c_49,c_50,c_51,c_52,c_54,c_57,c_58,c_59,c_2029,c_4494,c_11167,c_11393,c_12994])).

cnf(c_25,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1005,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1991,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1005])).

cnf(c_2083,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1991,c_983,c_1004])).

cnf(c_6843,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6828,c_2083])).

cnf(c_14901,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14896,c_6843])).

cnf(c_24,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1006,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1990,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1006])).

cnf(c_2088,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1990,c_983,c_1004])).

cnf(c_6844,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6828,c_2088])).

cnf(c_14902,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14896,c_6844])).

cnf(c_14906,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14901,c_14902])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 12:53:27 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 6.54/1.42  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.54/1.42  
% 6.54/1.42  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.54/1.42  
% 6.54/1.42  ------  iProver source info
% 6.54/1.42  
% 6.54/1.42  git: date: 2020-06-30 10:37:57 +0100
% 6.54/1.42  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.54/1.42  git: non_committed_changes: false
% 6.54/1.42  git: last_make_outside_of_git: false
% 6.54/1.42  
% 6.54/1.42  ------ 
% 6.54/1.42  
% 6.54/1.42  ------ Input Options
% 6.54/1.42  
% 6.54/1.42  --out_options                           all
% 6.54/1.42  --tptp_safe_out                         true
% 6.54/1.42  --problem_path                          ""
% 6.54/1.42  --include_path                          ""
% 6.54/1.42  --clausifier                            res/vclausify_rel
% 6.54/1.42  --clausifier_options                    --mode clausify
% 6.54/1.42  --stdin                                 false
% 6.54/1.42  --stats_out                             all
% 6.54/1.42  
% 6.54/1.42  ------ General Options
% 6.54/1.42  
% 6.54/1.42  --fof                                   false
% 6.54/1.42  --time_out_real                         305.
% 6.54/1.42  --time_out_virtual                      -1.
% 6.54/1.42  --symbol_type_check                     false
% 6.54/1.42  --clausify_out                          false
% 6.54/1.42  --sig_cnt_out                           false
% 6.54/1.42  --trig_cnt_out                          false
% 6.54/1.42  --trig_cnt_out_tolerance                1.
% 6.54/1.42  --trig_cnt_out_sk_spl                   false
% 6.54/1.42  --abstr_cl_out                          false
% 6.54/1.42  
% 6.54/1.42  ------ Global Options
% 6.54/1.42  
% 6.54/1.42  --schedule                              default
% 6.54/1.42  --add_important_lit                     false
% 6.54/1.42  --prop_solver_per_cl                    1000
% 6.54/1.42  --min_unsat_core                        false
% 6.54/1.42  --soft_assumptions                      false
% 6.54/1.42  --soft_lemma_size                       3
% 6.54/1.42  --prop_impl_unit_size                   0
% 6.54/1.42  --prop_impl_unit                        []
% 6.54/1.42  --share_sel_clauses                     true
% 6.54/1.42  --reset_solvers                         false
% 6.54/1.42  --bc_imp_inh                            [conj_cone]
% 6.54/1.42  --conj_cone_tolerance                   3.
% 6.54/1.42  --extra_neg_conj                        none
% 6.54/1.42  --large_theory_mode                     true
% 6.54/1.42  --prolific_symb_bound                   200
% 6.54/1.42  --lt_threshold                          2000
% 6.54/1.42  --clause_weak_htbl                      true
% 6.54/1.42  --gc_record_bc_elim                     false
% 6.54/1.42  
% 6.54/1.42  ------ Preprocessing Options
% 6.54/1.42  
% 6.54/1.42  --preprocessing_flag                    true
% 6.54/1.42  --time_out_prep_mult                    0.1
% 6.54/1.42  --splitting_mode                        input
% 6.54/1.42  --splitting_grd                         true
% 6.54/1.42  --splitting_cvd                         false
% 6.54/1.42  --splitting_cvd_svl                     false
% 6.54/1.42  --splitting_nvd                         32
% 6.54/1.42  --sub_typing                            true
% 6.54/1.42  --prep_gs_sim                           true
% 6.54/1.42  --prep_unflatten                        true
% 6.54/1.42  --prep_res_sim                          true
% 6.54/1.42  --prep_upred                            true
% 6.54/1.42  --prep_sem_filter                       exhaustive
% 6.54/1.42  --prep_sem_filter_out                   false
% 6.54/1.42  --pred_elim                             true
% 6.54/1.42  --res_sim_input                         true
% 6.54/1.42  --eq_ax_congr_red                       true
% 6.54/1.42  --pure_diseq_elim                       true
% 6.54/1.42  --brand_transform                       false
% 6.54/1.42  --non_eq_to_eq                          false
% 6.54/1.42  --prep_def_merge                        true
% 6.54/1.42  --prep_def_merge_prop_impl              false
% 6.54/1.42  --prep_def_merge_mbd                    true
% 6.54/1.42  --prep_def_merge_tr_red                 false
% 6.54/1.42  --prep_def_merge_tr_cl                  false
% 6.54/1.42  --smt_preprocessing                     true
% 6.54/1.42  --smt_ac_axioms                         fast
% 6.54/1.42  --preprocessed_out                      false
% 6.54/1.42  --preprocessed_stats                    false
% 6.54/1.42  
% 6.54/1.42  ------ Abstraction refinement Options
% 6.54/1.42  
% 6.54/1.42  --abstr_ref                             []
% 6.54/1.42  --abstr_ref_prep                        false
% 6.54/1.42  --abstr_ref_until_sat                   false
% 6.54/1.42  --abstr_ref_sig_restrict                funpre
% 6.54/1.42  --abstr_ref_af_restrict_to_split_sk     false
% 6.54/1.42  --abstr_ref_under                       []
% 6.54/1.42  
% 6.54/1.42  ------ SAT Options
% 6.54/1.42  
% 6.54/1.42  --sat_mode                              false
% 6.54/1.42  --sat_fm_restart_options                ""
% 6.54/1.42  --sat_gr_def                            false
% 6.54/1.42  --sat_epr_types                         true
% 6.54/1.42  --sat_non_cyclic_types                  false
% 6.54/1.42  --sat_finite_models                     false
% 6.54/1.42  --sat_fm_lemmas                         false
% 6.54/1.42  --sat_fm_prep                           false
% 6.54/1.42  --sat_fm_uc_incr                        true
% 6.54/1.42  --sat_out_model                         small
% 6.54/1.42  --sat_out_clauses                       false
% 6.54/1.42  
% 6.54/1.42  ------ QBF Options
% 6.54/1.42  
% 6.54/1.42  --qbf_mode                              false
% 6.54/1.42  --qbf_elim_univ                         false
% 6.54/1.42  --qbf_dom_inst                          none
% 6.54/1.42  --qbf_dom_pre_inst                      false
% 6.54/1.42  --qbf_sk_in                             false
% 6.54/1.42  --qbf_pred_elim                         true
% 6.54/1.42  --qbf_split                             512
% 6.54/1.42  
% 6.54/1.42  ------ BMC1 Options
% 6.54/1.42  
% 6.54/1.42  --bmc1_incremental                      false
% 6.54/1.42  --bmc1_axioms                           reachable_all
% 6.54/1.42  --bmc1_min_bound                        0
% 6.54/1.42  --bmc1_max_bound                        -1
% 6.54/1.42  --bmc1_max_bound_default                -1
% 6.54/1.42  --bmc1_symbol_reachability              true
% 6.54/1.42  --bmc1_property_lemmas                  false
% 6.54/1.42  --bmc1_k_induction                      false
% 6.54/1.42  --bmc1_non_equiv_states                 false
% 6.54/1.42  --bmc1_deadlock                         false
% 6.54/1.42  --bmc1_ucm                              false
% 6.54/1.42  --bmc1_add_unsat_core                   none
% 6.54/1.42  --bmc1_unsat_core_children              false
% 6.54/1.42  --bmc1_unsat_core_extrapolate_axioms    false
% 6.54/1.42  --bmc1_out_stat                         full
% 6.54/1.42  --bmc1_ground_init                      false
% 6.54/1.42  --bmc1_pre_inst_next_state              false
% 6.54/1.42  --bmc1_pre_inst_state                   false
% 6.54/1.42  --bmc1_pre_inst_reach_state             false
% 6.54/1.42  --bmc1_out_unsat_core                   false
% 6.54/1.42  --bmc1_aig_witness_out                  false
% 6.54/1.42  --bmc1_verbose                          false
% 6.54/1.42  --bmc1_dump_clauses_tptp                false
% 6.54/1.42  --bmc1_dump_unsat_core_tptp             false
% 6.54/1.42  --bmc1_dump_file                        -
% 6.54/1.42  --bmc1_ucm_expand_uc_limit              128
% 6.54/1.42  --bmc1_ucm_n_expand_iterations          6
% 6.54/1.42  --bmc1_ucm_extend_mode                  1
% 6.54/1.42  --bmc1_ucm_init_mode                    2
% 6.54/1.42  --bmc1_ucm_cone_mode                    none
% 6.54/1.42  --bmc1_ucm_reduced_relation_type        0
% 6.54/1.42  --bmc1_ucm_relax_model                  4
% 6.54/1.42  --bmc1_ucm_full_tr_after_sat            true
% 6.54/1.42  --bmc1_ucm_expand_neg_assumptions       false
% 6.54/1.42  --bmc1_ucm_layered_model                none
% 6.54/1.42  --bmc1_ucm_max_lemma_size               10
% 6.54/1.42  
% 6.54/1.42  ------ AIG Options
% 6.54/1.42  
% 6.54/1.42  --aig_mode                              false
% 6.54/1.42  
% 6.54/1.42  ------ Instantiation Options
% 6.54/1.42  
% 6.54/1.42  --instantiation_flag                    true
% 6.54/1.42  --inst_sos_flag                         false
% 6.54/1.42  --inst_sos_phase                        true
% 6.54/1.42  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.54/1.42  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.54/1.42  --inst_lit_sel_side                     num_symb
% 6.54/1.42  --inst_solver_per_active                1400
% 6.54/1.42  --inst_solver_calls_frac                1.
% 6.54/1.42  --inst_passive_queue_type               priority_queues
% 6.54/1.42  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.54/1.42  --inst_passive_queues_freq              [25;2]
% 6.54/1.42  --inst_dismatching                      true
% 6.54/1.42  --inst_eager_unprocessed_to_passive     true
% 6.54/1.42  --inst_prop_sim_given                   true
% 6.54/1.42  --inst_prop_sim_new                     false
% 6.54/1.42  --inst_subs_new                         false
% 6.54/1.42  --inst_eq_res_simp                      false
% 6.54/1.42  --inst_subs_given                       false
% 6.54/1.42  --inst_orphan_elimination               true
% 6.54/1.42  --inst_learning_loop_flag               true
% 6.54/1.42  --inst_learning_start                   3000
% 6.54/1.42  --inst_learning_factor                  2
% 6.54/1.42  --inst_start_prop_sim_after_learn       3
% 6.54/1.42  --inst_sel_renew                        solver
% 6.54/1.42  --inst_lit_activity_flag                true
% 6.54/1.42  --inst_restr_to_given                   false
% 6.54/1.42  --inst_activity_threshold               500
% 6.54/1.42  --inst_out_proof                        true
% 6.54/1.42  
% 6.54/1.42  ------ Resolution Options
% 6.54/1.42  
% 6.54/1.42  --resolution_flag                       true
% 6.54/1.42  --res_lit_sel                           adaptive
% 6.54/1.42  --res_lit_sel_side                      none
% 6.54/1.42  --res_ordering                          kbo
% 6.54/1.42  --res_to_prop_solver                    active
% 6.54/1.42  --res_prop_simpl_new                    false
% 6.54/1.42  --res_prop_simpl_given                  true
% 6.54/1.42  --res_passive_queue_type                priority_queues
% 6.54/1.42  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.54/1.42  --res_passive_queues_freq               [15;5]
% 6.54/1.42  --res_forward_subs                      full
% 6.54/1.42  --res_backward_subs                     full
% 6.54/1.42  --res_forward_subs_resolution           true
% 6.54/1.42  --res_backward_subs_resolution          true
% 6.54/1.42  --res_orphan_elimination                true
% 6.54/1.42  --res_time_limit                        2.
% 6.54/1.42  --res_out_proof                         true
% 6.54/1.42  
% 6.54/1.42  ------ Superposition Options
% 6.54/1.42  
% 6.54/1.42  --superposition_flag                    true
% 6.54/1.42  --sup_passive_queue_type                priority_queues
% 6.54/1.42  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.54/1.42  --sup_passive_queues_freq               [8;1;4]
% 6.54/1.42  --demod_completeness_check              fast
% 6.54/1.42  --demod_use_ground                      true
% 6.54/1.42  --sup_to_prop_solver                    passive
% 6.54/1.42  --sup_prop_simpl_new                    true
% 6.54/1.42  --sup_prop_simpl_given                  true
% 6.54/1.42  --sup_fun_splitting                     false
% 6.54/1.42  --sup_smt_interval                      50000
% 6.54/1.42  
% 6.54/1.42  ------ Superposition Simplification Setup
% 6.54/1.42  
% 6.54/1.42  --sup_indices_passive                   []
% 6.54/1.42  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.54/1.42  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.54/1.42  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.54/1.42  --sup_full_triv                         [TrivRules;PropSubs]
% 6.54/1.42  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.54/1.42  --sup_full_bw                           [BwDemod]
% 6.54/1.42  --sup_immed_triv                        [TrivRules]
% 6.54/1.42  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.54/1.42  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.54/1.42  --sup_immed_bw_main                     []
% 6.54/1.42  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.54/1.42  --sup_input_triv                        [Unflattening;TrivRules]
% 6.54/1.42  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.54/1.42  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.54/1.42  
% 6.54/1.42  ------ Combination Options
% 6.54/1.42  
% 6.54/1.42  --comb_res_mult                         3
% 6.54/1.42  --comb_sup_mult                         2
% 6.54/1.42  --comb_inst_mult                        10
% 6.54/1.42  
% 6.54/1.42  ------ Debug Options
% 6.54/1.42  
% 6.54/1.42  --dbg_backtrace                         false
% 6.54/1.42  --dbg_dump_prop_clauses                 false
% 6.54/1.42  --dbg_dump_prop_clauses_file            -
% 6.54/1.42  --dbg_out_stat                          false
% 6.54/1.42  ------ Parsing...
% 6.54/1.42  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.54/1.42  
% 6.54/1.42  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 6.54/1.42  
% 6.54/1.42  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.54/1.42  
% 6.54/1.42  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.54/1.42  ------ Proving...
% 6.54/1.42  ------ Problem Properties 
% 6.54/1.42  
% 6.54/1.42  
% 6.54/1.42  clauses                                 40
% 6.54/1.42  conjectures                             22
% 6.54/1.42  EPR                                     18
% 6.54/1.42  Horn                                    34
% 6.54/1.42  unary                                   21
% 6.54/1.42  binary                                  4
% 6.54/1.42  lits                                    141
% 6.54/1.42  lits eq                                 6
% 6.54/1.42  fd_pure                                 0
% 6.54/1.42  fd_pseudo                               0
% 6.54/1.42  fd_cond                                 0
% 6.54/1.42  fd_pseudo_cond                          1
% 6.54/1.42  AC symbols                              0
% 6.54/1.42  
% 6.54/1.42  ------ Schedule dynamic 5 is on 
% 6.54/1.42  
% 6.54/1.42  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.54/1.42  
% 6.54/1.42  
% 6.54/1.42  ------ 
% 6.54/1.42  Current options:
% 6.54/1.42  ------ 
% 6.54/1.42  
% 6.54/1.42  ------ Input Options
% 6.54/1.42  
% 6.54/1.42  --out_options                           all
% 6.54/1.42  --tptp_safe_out                         true
% 6.54/1.42  --problem_path                          ""
% 6.54/1.42  --include_path                          ""
% 6.54/1.42  --clausifier                            res/vclausify_rel
% 6.54/1.42  --clausifier_options                    --mode clausify
% 6.54/1.42  --stdin                                 false
% 6.54/1.42  --stats_out                             all
% 6.54/1.42  
% 6.54/1.42  ------ General Options
% 6.54/1.42  
% 6.54/1.42  --fof                                   false
% 6.54/1.42  --time_out_real                         305.
% 6.54/1.42  --time_out_virtual                      -1.
% 6.54/1.42  --symbol_type_check                     false
% 6.54/1.42  --clausify_out                          false
% 6.54/1.42  --sig_cnt_out                           false
% 6.54/1.42  --trig_cnt_out                          false
% 6.54/1.42  --trig_cnt_out_tolerance                1.
% 6.54/1.42  --trig_cnt_out_sk_spl                   false
% 6.54/1.42  --abstr_cl_out                          false
% 6.54/1.42  
% 6.54/1.42  ------ Global Options
% 6.54/1.42  
% 6.54/1.42  --schedule                              default
% 6.54/1.42  --add_important_lit                     false
% 6.54/1.42  --prop_solver_per_cl                    1000
% 6.54/1.42  --min_unsat_core                        false
% 6.54/1.42  --soft_assumptions                      false
% 6.54/1.42  --soft_lemma_size                       3
% 6.54/1.42  --prop_impl_unit_size                   0
% 6.54/1.42  --prop_impl_unit                        []
% 6.54/1.42  --share_sel_clauses                     true
% 6.54/1.42  --reset_solvers                         false
% 6.54/1.42  --bc_imp_inh                            [conj_cone]
% 6.54/1.42  --conj_cone_tolerance                   3.
% 6.54/1.42  --extra_neg_conj                        none
% 6.54/1.42  --large_theory_mode                     true
% 6.54/1.42  --prolific_symb_bound                   200
% 6.54/1.42  --lt_threshold                          2000
% 6.54/1.42  --clause_weak_htbl                      true
% 6.54/1.42  --gc_record_bc_elim                     false
% 6.54/1.42  
% 6.54/1.42  ------ Preprocessing Options
% 6.54/1.42  
% 6.54/1.42  --preprocessing_flag                    true
% 6.54/1.42  --time_out_prep_mult                    0.1
% 6.54/1.42  --splitting_mode                        input
% 6.54/1.42  --splitting_grd                         true
% 6.54/1.42  --splitting_cvd                         false
% 6.54/1.42  --splitting_cvd_svl                     false
% 6.54/1.42  --splitting_nvd                         32
% 6.54/1.42  --sub_typing                            true
% 6.54/1.42  --prep_gs_sim                           true
% 6.54/1.42  --prep_unflatten                        true
% 6.54/1.42  --prep_res_sim                          true
% 6.54/1.42  --prep_upred                            true
% 6.54/1.42  --prep_sem_filter                       exhaustive
% 6.54/1.42  --prep_sem_filter_out                   false
% 6.54/1.42  --pred_elim                             true
% 6.54/1.42  --res_sim_input                         true
% 6.54/1.42  --eq_ax_congr_red                       true
% 6.54/1.42  --pure_diseq_elim                       true
% 6.54/1.42  --brand_transform                       false
% 6.54/1.42  --non_eq_to_eq                          false
% 6.54/1.42  --prep_def_merge                        true
% 6.54/1.42  --prep_def_merge_prop_impl              false
% 6.54/1.42  --prep_def_merge_mbd                    true
% 6.54/1.42  --prep_def_merge_tr_red                 false
% 6.54/1.42  --prep_def_merge_tr_cl                  false
% 6.54/1.42  --smt_preprocessing                     true
% 6.54/1.42  --smt_ac_axioms                         fast
% 6.54/1.42  --preprocessed_out                      false
% 6.54/1.42  --preprocessed_stats                    false
% 6.54/1.42  
% 6.54/1.42  ------ Abstraction refinement Options
% 6.54/1.42  
% 6.54/1.42  --abstr_ref                             []
% 6.54/1.42  --abstr_ref_prep                        false
% 6.54/1.42  --abstr_ref_until_sat                   false
% 6.54/1.42  --abstr_ref_sig_restrict                funpre
% 6.54/1.42  --abstr_ref_af_restrict_to_split_sk     false
% 6.54/1.42  --abstr_ref_under                       []
% 6.54/1.42  
% 6.54/1.42  ------ SAT Options
% 6.54/1.42  
% 6.54/1.42  --sat_mode                              false
% 6.54/1.42  --sat_fm_restart_options                ""
% 6.54/1.42  --sat_gr_def                            false
% 6.54/1.42  --sat_epr_types                         true
% 6.54/1.42  --sat_non_cyclic_types                  false
% 6.54/1.42  --sat_finite_models                     false
% 6.54/1.42  --sat_fm_lemmas                         false
% 6.54/1.42  --sat_fm_prep                           false
% 6.54/1.42  --sat_fm_uc_incr                        true
% 6.54/1.42  --sat_out_model                         small
% 6.54/1.42  --sat_out_clauses                       false
% 6.54/1.42  
% 6.54/1.42  ------ QBF Options
% 6.54/1.42  
% 6.54/1.42  --qbf_mode                              false
% 6.54/1.42  --qbf_elim_univ                         false
% 6.54/1.42  --qbf_dom_inst                          none
% 6.54/1.42  --qbf_dom_pre_inst                      false
% 6.54/1.42  --qbf_sk_in                             false
% 6.54/1.42  --qbf_pred_elim                         true
% 6.54/1.42  --qbf_split                             512
% 6.54/1.42  
% 6.54/1.42  ------ BMC1 Options
% 6.54/1.42  
% 6.54/1.42  --bmc1_incremental                      false
% 6.54/1.42  --bmc1_axioms                           reachable_all
% 6.54/1.42  --bmc1_min_bound                        0
% 6.54/1.42  --bmc1_max_bound                        -1
% 6.54/1.42  --bmc1_max_bound_default                -1
% 6.54/1.42  --bmc1_symbol_reachability              true
% 6.54/1.42  --bmc1_property_lemmas                  false
% 6.54/1.42  --bmc1_k_induction                      false
% 6.54/1.42  --bmc1_non_equiv_states                 false
% 6.54/1.42  --bmc1_deadlock                         false
% 6.54/1.42  --bmc1_ucm                              false
% 6.54/1.42  --bmc1_add_unsat_core                   none
% 6.54/1.42  --bmc1_unsat_core_children              false
% 6.54/1.42  --bmc1_unsat_core_extrapolate_axioms    false
% 6.54/1.42  --bmc1_out_stat                         full
% 6.54/1.42  --bmc1_ground_init                      false
% 6.54/1.42  --bmc1_pre_inst_next_state              false
% 6.54/1.42  --bmc1_pre_inst_state                   false
% 6.54/1.42  --bmc1_pre_inst_reach_state             false
% 6.54/1.42  --bmc1_out_unsat_core                   false
% 6.54/1.42  --bmc1_aig_witness_out                  false
% 6.54/1.42  --bmc1_verbose                          false
% 6.54/1.42  --bmc1_dump_clauses_tptp                false
% 6.54/1.42  --bmc1_dump_unsat_core_tptp             false
% 6.54/1.42  --bmc1_dump_file                        -
% 6.54/1.42  --bmc1_ucm_expand_uc_limit              128
% 6.54/1.42  --bmc1_ucm_n_expand_iterations          6
% 6.54/1.42  --bmc1_ucm_extend_mode                  1
% 6.54/1.42  --bmc1_ucm_init_mode                    2
% 6.54/1.42  --bmc1_ucm_cone_mode                    none
% 6.54/1.42  --bmc1_ucm_reduced_relation_type        0
% 6.54/1.42  --bmc1_ucm_relax_model                  4
% 6.54/1.42  --bmc1_ucm_full_tr_after_sat            true
% 6.54/1.42  --bmc1_ucm_expand_neg_assumptions       false
% 6.54/1.42  --bmc1_ucm_layered_model                none
% 6.54/1.42  --bmc1_ucm_max_lemma_size               10
% 6.54/1.42  
% 6.54/1.42  ------ AIG Options
% 6.54/1.42  
% 6.54/1.42  --aig_mode                              false
% 6.54/1.42  
% 6.54/1.42  ------ Instantiation Options
% 6.54/1.42  
% 6.54/1.42  --instantiation_flag                    true
% 6.54/1.42  --inst_sos_flag                         false
% 6.54/1.42  --inst_sos_phase                        true
% 6.54/1.42  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.54/1.42  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.54/1.42  --inst_lit_sel_side                     none
% 6.54/1.42  --inst_solver_per_active                1400
% 6.54/1.42  --inst_solver_calls_frac                1.
% 6.54/1.42  --inst_passive_queue_type               priority_queues
% 6.54/1.42  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.54/1.42  --inst_passive_queues_freq              [25;2]
% 6.54/1.42  --inst_dismatching                      true
% 6.54/1.42  --inst_eager_unprocessed_to_passive     true
% 6.54/1.42  --inst_prop_sim_given                   true
% 6.54/1.42  --inst_prop_sim_new                     false
% 6.54/1.42  --inst_subs_new                         false
% 6.54/1.42  --inst_eq_res_simp                      false
% 6.54/1.42  --inst_subs_given                       false
% 6.54/1.42  --inst_orphan_elimination               true
% 6.54/1.42  --inst_learning_loop_flag               true
% 6.54/1.42  --inst_learning_start                   3000
% 6.54/1.42  --inst_learning_factor                  2
% 6.54/1.42  --inst_start_prop_sim_after_learn       3
% 6.54/1.42  --inst_sel_renew                        solver
% 6.54/1.42  --inst_lit_activity_flag                true
% 6.54/1.42  --inst_restr_to_given                   false
% 6.54/1.42  --inst_activity_threshold               500
% 6.54/1.42  --inst_out_proof                        true
% 6.54/1.42  
% 6.54/1.42  ------ Resolution Options
% 6.54/1.42  
% 6.54/1.42  --resolution_flag                       false
% 6.54/1.42  --res_lit_sel                           adaptive
% 6.54/1.42  --res_lit_sel_side                      none
% 6.54/1.42  --res_ordering                          kbo
% 6.54/1.42  --res_to_prop_solver                    active
% 6.54/1.42  --res_prop_simpl_new                    false
% 6.54/1.42  --res_prop_simpl_given                  true
% 6.54/1.42  --res_passive_queue_type                priority_queues
% 6.54/1.42  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.54/1.42  --res_passive_queues_freq               [15;5]
% 6.54/1.42  --res_forward_subs                      full
% 6.54/1.42  --res_backward_subs                     full
% 6.54/1.42  --res_forward_subs_resolution           true
% 6.54/1.42  --res_backward_subs_resolution          true
% 6.54/1.42  --res_orphan_elimination                true
% 6.54/1.42  --res_time_limit                        2.
% 6.54/1.42  --res_out_proof                         true
% 6.54/1.42  
% 6.54/1.42  ------ Superposition Options
% 6.54/1.42  
% 6.54/1.42  --superposition_flag                    true
% 6.54/1.42  --sup_passive_queue_type                priority_queues
% 6.54/1.42  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.54/1.42  --sup_passive_queues_freq               [8;1;4]
% 6.54/1.42  --demod_completeness_check              fast
% 6.54/1.42  --demod_use_ground                      true
% 6.54/1.42  --sup_to_prop_solver                    passive
% 6.54/1.42  --sup_prop_simpl_new                    true
% 6.54/1.42  --sup_prop_simpl_given                  true
% 6.54/1.42  --sup_fun_splitting                     false
% 6.54/1.42  --sup_smt_interval                      50000
% 6.54/1.42  
% 6.54/1.42  ------ Superposition Simplification Setup
% 6.54/1.42  
% 6.54/1.42  --sup_indices_passive                   []
% 6.54/1.42  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.54/1.42  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.54/1.42  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.54/1.42  --sup_full_triv                         [TrivRules;PropSubs]
% 6.54/1.42  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.54/1.42  --sup_full_bw                           [BwDemod]
% 6.54/1.42  --sup_immed_triv                        [TrivRules]
% 6.54/1.42  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.54/1.42  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.54/1.42  --sup_immed_bw_main                     []
% 6.54/1.42  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.54/1.42  --sup_input_triv                        [Unflattening;TrivRules]
% 6.54/1.42  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.54/1.42  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.54/1.42  
% 6.54/1.42  ------ Combination Options
% 6.54/1.42  
% 6.54/1.42  --comb_res_mult                         3
% 6.54/1.42  --comb_sup_mult                         2
% 6.54/1.42  --comb_inst_mult                        10
% 6.54/1.42  
% 6.54/1.42  ------ Debug Options
% 6.54/1.42  
% 6.54/1.42  --dbg_backtrace                         false
% 6.54/1.42  --dbg_dump_prop_clauses                 false
% 6.54/1.42  --dbg_dump_prop_clauses_file            -
% 6.54/1.42  --dbg_out_stat                          false
% 6.54/1.42  
% 6.54/1.42  
% 6.54/1.42  
% 6.54/1.42  
% 6.54/1.42  ------ Proving...
% 6.54/1.42  
% 6.54/1.42  
% 6.54/1.42  % SZS status Theorem for theBenchmark.p
% 6.54/1.42  
% 6.54/1.42   Resolution empty clause
% 6.54/1.42  
% 6.54/1.42  % SZS output start CNFRefutation for theBenchmark.p
% 6.54/1.42  
% 6.54/1.42  fof(f17,conjecture,(
% 6.54/1.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 6.54/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.54/1.43  
% 6.54/1.43  fof(f18,negated_conjecture,(
% 6.54/1.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 6.54/1.43    inference(negated_conjecture,[],[f17])).
% 6.54/1.43  
% 6.54/1.43  fof(f47,plain,(
% 6.54/1.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 6.54/1.43    inference(ennf_transformation,[],[f18])).
% 6.54/1.43  
% 6.54/1.43  fof(f48,plain,(
% 6.54/1.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 6.54/1.43    inference(flattening,[],[f47])).
% 6.54/1.43  
% 6.54/1.43  fof(f52,plain,(
% 6.54/1.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 6.54/1.43    inference(nnf_transformation,[],[f48])).
% 6.54/1.43  
% 6.54/1.43  fof(f53,plain,(
% 6.54/1.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 6.54/1.43    inference(flattening,[],[f52])).
% 6.54/1.43  
% 6.54/1.43  fof(f60,plain,(
% 6.54/1.43    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK6) & X0 = X3 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 6.54/1.43    introduced(choice_axiom,[])).
% 6.54/1.43  
% 6.54/1.43  fof(f59,plain,(
% 6.54/1.43    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 6.54/1.43    introduced(choice_axiom,[])).
% 6.54/1.43  
% 6.54/1.43  fof(f58,plain,(
% 6.54/1.43    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 6.54/1.43    introduced(choice_axiom,[])).
% 6.54/1.43  
% 6.54/1.43  fof(f57,plain,(
% 6.54/1.43    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK3),u1_struct_0(X1),X4,X6) & sK3 = X0 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 6.54/1.43    introduced(choice_axiom,[])).
% 6.54/1.43  
% 6.54/1.43  fof(f56,plain,(
% 6.54/1.43    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK2),X5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X6),X5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK2),X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 6.54/1.43    introduced(choice_axiom,[])).
% 6.54/1.43  
% 6.54/1.43  fof(f55,plain,(
% 6.54/1.43    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 6.54/1.43    introduced(choice_axiom,[])).
% 6.54/1.43  
% 6.54/1.43  fof(f54,plain,(
% 6.54/1.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 6.54/1.43    introduced(choice_axiom,[])).
% 6.54/1.43  
% 6.54/1.43  fof(f61,plain,(
% 6.54/1.43    (((((((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) & sK0 = sK3 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 6.54/1.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f53,f60,f59,f58,f57,f56,f55,f54])).
% 6.54/1.43  
% 6.54/1.43  fof(f95,plain,(
% 6.54/1.43    m1_pre_topc(sK3,sK0)),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f105,plain,(
% 6.54/1.43    sK0 = sK3),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f104,plain,(
% 6.54/1.43    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f11,axiom,(
% 6.54/1.43    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 6.54/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.54/1.43  
% 6.54/1.43  fof(f35,plain,(
% 6.54/1.43    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 6.54/1.43    inference(ennf_transformation,[],[f11])).
% 6.54/1.43  
% 6.54/1.43  fof(f36,plain,(
% 6.54/1.43    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 6.54/1.43    inference(flattening,[],[f35])).
% 6.54/1.43  
% 6.54/1.43  fof(f51,plain,(
% 6.54/1.43    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 6.54/1.43    inference(nnf_transformation,[],[f36])).
% 6.54/1.43  
% 6.54/1.43  fof(f75,plain,(
% 6.54/1.43    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 6.54/1.43    inference(cnf_transformation,[],[f51])).
% 6.54/1.43  
% 6.54/1.43  fof(f106,plain,(
% 6.54/1.43    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f89,plain,(
% 6.54/1.43    ~v2_struct_0(sK1)),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f91,plain,(
% 6.54/1.43    l1_pre_topc(sK1)),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f96,plain,(
% 6.54/1.43    v1_funct_1(sK4)),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f97,plain,(
% 6.54/1.43    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f98,plain,(
% 6.54/1.43    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f102,plain,(
% 6.54/1.43    v1_funct_1(sK6)),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f103,plain,(
% 6.54/1.43    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f10,axiom,(
% 6.54/1.43    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 6.54/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.54/1.43  
% 6.54/1.43  fof(f33,plain,(
% 6.54/1.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 6.54/1.43    inference(ennf_transformation,[],[f10])).
% 6.54/1.43  
% 6.54/1.43  fof(f34,plain,(
% 6.54/1.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 6.54/1.43    inference(flattening,[],[f33])).
% 6.54/1.43  
% 6.54/1.43  fof(f74,plain,(
% 6.54/1.43    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 6.54/1.43    inference(cnf_transformation,[],[f34])).
% 6.54/1.43  
% 6.54/1.43  fof(f8,axiom,(
% 6.54/1.43    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 6.54/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.54/1.43  
% 6.54/1.43  fof(f31,plain,(
% 6.54/1.43    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 6.54/1.43    inference(ennf_transformation,[],[f8])).
% 6.54/1.43  
% 6.54/1.43  fof(f72,plain,(
% 6.54/1.43    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 6.54/1.43    inference(cnf_transformation,[],[f31])).
% 6.54/1.43  
% 6.54/1.43  fof(f12,axiom,(
% 6.54/1.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 6.54/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.54/1.43  
% 6.54/1.43  fof(f37,plain,(
% 6.54/1.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.54/1.43    inference(ennf_transformation,[],[f12])).
% 6.54/1.43  
% 6.54/1.43  fof(f38,plain,(
% 6.54/1.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.54/1.43    inference(flattening,[],[f37])).
% 6.54/1.43  
% 6.54/1.43  fof(f77,plain,(
% 6.54/1.43    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.54/1.43    inference(cnf_transformation,[],[f38])).
% 6.54/1.43  
% 6.54/1.43  fof(f6,axiom,(
% 6.54/1.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 6.54/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.54/1.43  
% 6.54/1.43  fof(f27,plain,(
% 6.54/1.43    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 6.54/1.43    inference(ennf_transformation,[],[f6])).
% 6.54/1.43  
% 6.54/1.43  fof(f28,plain,(
% 6.54/1.43    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 6.54/1.43    inference(flattening,[],[f27])).
% 6.54/1.43  
% 6.54/1.43  fof(f69,plain,(
% 6.54/1.43    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.54/1.43    inference(cnf_transformation,[],[f28])).
% 6.54/1.43  
% 6.54/1.43  fof(f86,plain,(
% 6.54/1.43    ~v2_struct_0(sK0)),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f87,plain,(
% 6.54/1.43    v2_pre_topc(sK0)),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f88,plain,(
% 6.54/1.43    l1_pre_topc(sK0)),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f90,plain,(
% 6.54/1.43    v2_pre_topc(sK1)),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f4,axiom,(
% 6.54/1.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.54/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.54/1.43  
% 6.54/1.43  fof(f19,plain,(
% 6.54/1.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 6.54/1.43    inference(pure_predicate_removal,[],[f4])).
% 6.54/1.43  
% 6.54/1.43  fof(f24,plain,(
% 6.54/1.43    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.54/1.43    inference(ennf_transformation,[],[f19])).
% 6.54/1.43  
% 6.54/1.43  fof(f66,plain,(
% 6.54/1.43    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.54/1.43    inference(cnf_transformation,[],[f24])).
% 6.54/1.43  
% 6.54/1.43  fof(f1,axiom,(
% 6.54/1.43    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 6.54/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.54/1.43  
% 6.54/1.43  fof(f20,plain,(
% 6.54/1.43    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.54/1.43    inference(ennf_transformation,[],[f1])).
% 6.54/1.43  
% 6.54/1.43  fof(f49,plain,(
% 6.54/1.43    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.54/1.43    inference(nnf_transformation,[],[f20])).
% 6.54/1.43  
% 6.54/1.43  fof(f62,plain,(
% 6.54/1.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.54/1.43    inference(cnf_transformation,[],[f49])).
% 6.54/1.43  
% 6.54/1.43  fof(f3,axiom,(
% 6.54/1.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.54/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.54/1.43  
% 6.54/1.43  fof(f23,plain,(
% 6.54/1.43    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.54/1.43    inference(ennf_transformation,[],[f3])).
% 6.54/1.43  
% 6.54/1.43  fof(f65,plain,(
% 6.54/1.43    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.54/1.43    inference(cnf_transformation,[],[f23])).
% 6.54/1.43  
% 6.54/1.43  fof(f2,axiom,(
% 6.54/1.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 6.54/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.54/1.43  
% 6.54/1.43  fof(f21,plain,(
% 6.54/1.43    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.54/1.43    inference(ennf_transformation,[],[f2])).
% 6.54/1.43  
% 6.54/1.43  fof(f22,plain,(
% 6.54/1.43    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 6.54/1.43    inference(flattening,[],[f21])).
% 6.54/1.43  
% 6.54/1.43  fof(f64,plain,(
% 6.54/1.43    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 6.54/1.43    inference(cnf_transformation,[],[f22])).
% 6.54/1.43  
% 6.54/1.43  fof(f93,plain,(
% 6.54/1.43    m1_pre_topc(sK2,sK0)),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f15,axiom,(
% 6.54/1.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 6.54/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.54/1.43  
% 6.54/1.43  fof(f43,plain,(
% 6.54/1.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.54/1.43    inference(ennf_transformation,[],[f15])).
% 6.54/1.43  
% 6.54/1.43  fof(f44,plain,(
% 6.54/1.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.54/1.43    inference(flattening,[],[f43])).
% 6.54/1.43  
% 6.54/1.43  fof(f84,plain,(
% 6.54/1.43    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.54/1.43    inference(cnf_transformation,[],[f44])).
% 6.54/1.43  
% 6.54/1.43  fof(f16,axiom,(
% 6.54/1.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 6.54/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.54/1.43  
% 6.54/1.43  fof(f45,plain,(
% 6.54/1.43    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 6.54/1.43    inference(ennf_transformation,[],[f16])).
% 6.54/1.43  
% 6.54/1.43  fof(f46,plain,(
% 6.54/1.43    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.54/1.43    inference(flattening,[],[f45])).
% 6.54/1.43  
% 6.54/1.43  fof(f85,plain,(
% 6.54/1.43    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.54/1.43    inference(cnf_transformation,[],[f46])).
% 6.54/1.43  
% 6.54/1.43  fof(f92,plain,(
% 6.54/1.43    ~v2_struct_0(sK2)),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f13,axiom,(
% 6.54/1.43    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 6.54/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.54/1.43  
% 6.54/1.43  fof(f39,plain,(
% 6.54/1.43    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 6.54/1.43    inference(ennf_transformation,[],[f13])).
% 6.54/1.43  
% 6.54/1.43  fof(f40,plain,(
% 6.54/1.43    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 6.54/1.43    inference(flattening,[],[f39])).
% 6.54/1.43  
% 6.54/1.43  fof(f80,plain,(
% 6.54/1.43    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 6.54/1.43    inference(cnf_transformation,[],[f40])).
% 6.54/1.43  
% 6.54/1.43  fof(f9,axiom,(
% 6.54/1.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 6.54/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.54/1.43  
% 6.54/1.43  fof(f32,plain,(
% 6.54/1.43    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 6.54/1.43    inference(ennf_transformation,[],[f9])).
% 6.54/1.43  
% 6.54/1.43  fof(f73,plain,(
% 6.54/1.43    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 6.54/1.43    inference(cnf_transformation,[],[f32])).
% 6.54/1.43  
% 6.54/1.43  fof(f7,axiom,(
% 6.54/1.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 6.54/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.54/1.43  
% 6.54/1.43  fof(f29,plain,(
% 6.54/1.43    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.54/1.43    inference(ennf_transformation,[],[f7])).
% 6.54/1.43  
% 6.54/1.43  fof(f30,plain,(
% 6.54/1.43    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.54/1.43    inference(flattening,[],[f29])).
% 6.54/1.43  
% 6.54/1.43  fof(f50,plain,(
% 6.54/1.43    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.54/1.43    inference(nnf_transformation,[],[f30])).
% 6.54/1.43  
% 6.54/1.43  fof(f70,plain,(
% 6.54/1.43    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.54/1.43    inference(cnf_transformation,[],[f50])).
% 6.54/1.43  
% 6.54/1.43  fof(f79,plain,(
% 6.54/1.43    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 6.54/1.43    inference(cnf_transformation,[],[f40])).
% 6.54/1.43  
% 6.54/1.43  fof(f5,axiom,(
% 6.54/1.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 6.54/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.54/1.43  
% 6.54/1.43  fof(f25,plain,(
% 6.54/1.43    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 6.54/1.43    inference(ennf_transformation,[],[f5])).
% 6.54/1.43  
% 6.54/1.43  fof(f26,plain,(
% 6.54/1.43    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 6.54/1.43    inference(flattening,[],[f25])).
% 6.54/1.43  
% 6.54/1.43  fof(f67,plain,(
% 6.54/1.43    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.54/1.43    inference(cnf_transformation,[],[f26])).
% 6.54/1.43  
% 6.54/1.43  fof(f14,axiom,(
% 6.54/1.43    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 6.54/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.54/1.43  
% 6.54/1.43  fof(f41,plain,(
% 6.54/1.43    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.54/1.43    inference(ennf_transformation,[],[f14])).
% 6.54/1.43  
% 6.54/1.43  fof(f42,plain,(
% 6.54/1.43    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.54/1.43    inference(flattening,[],[f41])).
% 6.54/1.43  
% 6.54/1.43  fof(f82,plain,(
% 6.54/1.43    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.54/1.43    inference(cnf_transformation,[],[f42])).
% 6.54/1.43  
% 6.54/1.43  fof(f81,plain,(
% 6.54/1.43    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.54/1.43    inference(cnf_transformation,[],[f42])).
% 6.54/1.43  
% 6.54/1.43  fof(f83,plain,(
% 6.54/1.43    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.54/1.43    inference(cnf_transformation,[],[f42])).
% 6.54/1.43  
% 6.54/1.43  fof(f107,plain,(
% 6.54/1.43    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  fof(f108,plain,(
% 6.54/1.43    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 6.54/1.43    inference(cnf_transformation,[],[f61])).
% 6.54/1.43  
% 6.54/1.43  cnf(c_37,negated_conjecture,
% 6.54/1.43      ( m1_pre_topc(sK3,sK0) ),
% 6.54/1.43      inference(cnf_transformation,[],[f95]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_994,negated_conjecture,
% 6.54/1.43      ( m1_pre_topc(sK3,sK0) ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_37]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2001,plain,
% 6.54/1.43      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_994]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_27,negated_conjecture,
% 6.54/1.43      ( sK0 = sK3 ),
% 6.54/1.43      inference(cnf_transformation,[],[f105]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1004,negated_conjecture,
% 6.54/1.43      ( sK0 = sK3 ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_27]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2029,plain,
% 6.54/1.43      ( m1_pre_topc(sK0,sK0) = iProver_top ),
% 6.54/1.43      inference(light_normalisation,[status(thm)],[c_2001,c_1004]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_28,negated_conjecture,
% 6.54/1.43      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 6.54/1.43      inference(cnf_transformation,[],[f104]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1003,negated_conjecture,
% 6.54/1.43      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_28]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1992,plain,
% 6.54/1.43      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_1003]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_14,plain,
% 6.54/1.43      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 6.54/1.43      | ~ v1_funct_2(X5,X2,X3)
% 6.54/1.43      | ~ v1_funct_2(X4,X0,X1)
% 6.54/1.43      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 6.54/1.43      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.54/1.43      | v1_xboole_0(X1)
% 6.54/1.43      | v1_xboole_0(X3)
% 6.54/1.43      | ~ v1_funct_1(X5)
% 6.54/1.43      | ~ v1_funct_1(X4)
% 6.54/1.43      | X4 = X5 ),
% 6.54/1.43      inference(cnf_transformation,[],[f75]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_26,negated_conjecture,
% 6.54/1.43      ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
% 6.54/1.43      inference(cnf_transformation,[],[f106]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_636,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0,X1,X2)
% 6.54/1.43      | ~ v1_funct_2(X3,X4,X5)
% 6.54/1.43      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.54/1.43      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 6.54/1.43      | v1_xboole_0(X5)
% 6.54/1.43      | v1_xboole_0(X2)
% 6.54/1.43      | ~ v1_funct_1(X0)
% 6.54/1.43      | ~ v1_funct_1(X3)
% 6.54/1.43      | X3 = X0
% 6.54/1.43      | u1_struct_0(sK3) != X4
% 6.54/1.43      | u1_struct_0(sK0) != X1
% 6.54/1.43      | u1_struct_0(sK1) != X5
% 6.54/1.43      | u1_struct_0(sK1) != X2
% 6.54/1.43      | sK6 != X3
% 6.54/1.43      | sK4 != X0 ),
% 6.54/1.43      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_637,plain,
% 6.54/1.43      ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
% 6.54/1.43      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 6.54/1.43      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 6.54/1.43      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 6.54/1.43      | v1_xboole_0(u1_struct_0(sK1))
% 6.54/1.43      | ~ v1_funct_1(sK6)
% 6.54/1.43      | ~ v1_funct_1(sK4)
% 6.54/1.43      | sK6 = sK4 ),
% 6.54/1.43      inference(unflattening,[status(thm)],[c_636]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_43,negated_conjecture,
% 6.54/1.43      ( ~ v2_struct_0(sK1) ),
% 6.54/1.43      inference(cnf_transformation,[],[f89]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_41,negated_conjecture,
% 6.54/1.43      ( l1_pre_topc(sK1) ),
% 6.54/1.43      inference(cnf_transformation,[],[f91]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_36,negated_conjecture,
% 6.54/1.43      ( v1_funct_1(sK4) ),
% 6.54/1.43      inference(cnf_transformation,[],[f96]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_35,negated_conjecture,
% 6.54/1.43      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 6.54/1.43      inference(cnf_transformation,[],[f97]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_34,negated_conjecture,
% 6.54/1.43      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 6.54/1.43      inference(cnf_transformation,[],[f98]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_30,negated_conjecture,
% 6.54/1.43      ( v1_funct_1(sK6) ),
% 6.54/1.43      inference(cnf_transformation,[],[f102]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_29,negated_conjecture,
% 6.54/1.43      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 6.54/1.43      inference(cnf_transformation,[],[f103]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_12,plain,
% 6.54/1.43      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 6.54/1.43      inference(cnf_transformation,[],[f74]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_101,plain,
% 6.54/1.43      ( v2_struct_0(sK1)
% 6.54/1.43      | ~ v1_xboole_0(u1_struct_0(sK1))
% 6.54/1.43      | ~ l1_struct_0(sK1) ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_12]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_10,plain,
% 6.54/1.43      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 6.54/1.43      inference(cnf_transformation,[],[f72]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_105,plain,
% 6.54/1.43      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_10]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_639,plain,
% 6.54/1.43      ( sK6 = sK4 ),
% 6.54/1.43      inference(global_propositional_subsumption,
% 6.54/1.43                [status(thm)],
% 6.54/1.43                [c_637,c_43,c_41,c_36,c_35,c_34,c_30,c_29,c_28,c_101,c_105]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_983,plain,( sK6 = sK4 ),inference(subtyping,[status(esa)],[c_639]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2050,plain,
% 6.54/1.43      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 6.54/1.43      inference(light_normalisation,[status(thm)],[c_1992,c_983,c_1004]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_15,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 6.54/1.43      | ~ m1_pre_topc(X3,X1)
% 6.54/1.43      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 6.54/1.43      | ~ v2_pre_topc(X2)
% 6.54/1.43      | ~ v2_pre_topc(X1)
% 6.54/1.43      | v2_struct_0(X1)
% 6.54/1.43      | v2_struct_0(X2)
% 6.54/1.43      | ~ l1_pre_topc(X1)
% 6.54/1.43      | ~ l1_pre_topc(X2)
% 6.54/1.43      | ~ v1_funct_1(X0)
% 6.54/1.43      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 6.54/1.43      inference(cnf_transformation,[],[f77]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1015,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61))
% 6.54/1.43      | ~ m1_pre_topc(X2_61,X0_61)
% 6.54/1.43      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
% 6.54/1.43      | ~ v2_pre_topc(X1_61)
% 6.54/1.43      | ~ v2_pre_topc(X0_61)
% 6.54/1.43      | v2_struct_0(X1_61)
% 6.54/1.43      | v2_struct_0(X0_61)
% 6.54/1.43      | ~ l1_pre_topc(X1_61)
% 6.54/1.43      | ~ l1_pre_topc(X0_61)
% 6.54/1.43      | ~ v1_funct_1(X0_57)
% 6.54/1.43      | k2_partfun1(u1_struct_0(X0_61),u1_struct_0(X1_61),X0_57,u1_struct_0(X2_61)) = k2_tmap_1(X0_61,X1_61,X0_57,X2_61) ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_15]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1981,plain,
% 6.54/1.43      ( k2_partfun1(u1_struct_0(X0_61),u1_struct_0(X1_61),X0_57,u1_struct_0(X2_61)) = k2_tmap_1(X0_61,X1_61,X0_57,X2_61)
% 6.54/1.43      | v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61)) != iProver_top
% 6.54/1.43      | m1_pre_topc(X2_61,X0_61) != iProver_top
% 6.54/1.43      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61)))) != iProver_top
% 6.54/1.43      | v2_pre_topc(X1_61) != iProver_top
% 6.54/1.43      | v2_pre_topc(X0_61) != iProver_top
% 6.54/1.43      | v2_struct_0(X1_61) = iProver_top
% 6.54/1.43      | v2_struct_0(X0_61) = iProver_top
% 6.54/1.43      | l1_pre_topc(X1_61) != iProver_top
% 6.54/1.43      | l1_pre_topc(X0_61) != iProver_top
% 6.54/1.43      | v1_funct_1(X0_57) != iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_1015]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_4686,plain,
% 6.54/1.43      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_61)) = k2_tmap_1(sK0,sK1,sK4,X0_61)
% 6.54/1.43      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 6.54/1.43      | m1_pre_topc(X0_61,sK0) != iProver_top
% 6.54/1.43      | v2_pre_topc(sK0) != iProver_top
% 6.54/1.43      | v2_pre_topc(sK1) != iProver_top
% 6.54/1.43      | v2_struct_0(sK0) = iProver_top
% 6.54/1.43      | v2_struct_0(sK1) = iProver_top
% 6.54/1.43      | l1_pre_topc(sK0) != iProver_top
% 6.54/1.43      | l1_pre_topc(sK1) != iProver_top
% 6.54/1.43      | v1_funct_1(sK4) != iProver_top ),
% 6.54/1.43      inference(superposition,[status(thm)],[c_2050,c_1981]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_7,plain,
% 6.54/1.43      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.54/1.43      | ~ v1_funct_1(X0)
% 6.54/1.43      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 6.54/1.43      inference(cnf_transformation,[],[f69]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1020,plain,
% 6.54/1.43      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
% 6.54/1.43      | ~ v1_funct_1(X0_57)
% 6.54/1.43      | k2_partfun1(X0_60,X1_60,X0_57,X2_60) = k7_relat_1(X0_57,X2_60) ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_7]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1976,plain,
% 6.54/1.43      ( k2_partfun1(X0_60,X1_60,X0_57,X2_60) = k7_relat_1(X0_57,X2_60)
% 6.54/1.43      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) != iProver_top
% 6.54/1.43      | v1_funct_1(X0_57) != iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_1020]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_3099,plain,
% 6.54/1.43      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_60) = k7_relat_1(sK4,X0_60)
% 6.54/1.43      | v1_funct_1(sK4) != iProver_top ),
% 6.54/1.43      inference(superposition,[status(thm)],[c_2050,c_1976]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2456,plain,
% 6.54/1.43      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 6.54/1.43      | ~ v1_funct_1(sK4)
% 6.54/1.43      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_60) = k7_relat_1(sK4,X0_60) ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_1020]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_3759,plain,
% 6.54/1.43      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_60) = k7_relat_1(sK4,X0_60) ),
% 6.54/1.43      inference(global_propositional_subsumption,
% 6.54/1.43                [status(thm)],
% 6.54/1.43                [c_3099,c_36,c_34,c_2456]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_4755,plain,
% 6.54/1.43      ( k2_tmap_1(sK0,sK1,sK4,X0_61) = k7_relat_1(sK4,u1_struct_0(X0_61))
% 6.54/1.43      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 6.54/1.43      | m1_pre_topc(X0_61,sK0) != iProver_top
% 6.54/1.43      | v2_pre_topc(sK0) != iProver_top
% 6.54/1.43      | v2_pre_topc(sK1) != iProver_top
% 6.54/1.43      | v2_struct_0(sK0) = iProver_top
% 6.54/1.43      | v2_struct_0(sK1) = iProver_top
% 6.54/1.43      | l1_pre_topc(sK0) != iProver_top
% 6.54/1.43      | l1_pre_topc(sK1) != iProver_top
% 6.54/1.43      | v1_funct_1(sK4) != iProver_top ),
% 6.54/1.43      inference(demodulation,[status(thm)],[c_4686,c_3759]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_46,negated_conjecture,
% 6.54/1.43      ( ~ v2_struct_0(sK0) ),
% 6.54/1.43      inference(cnf_transformation,[],[f86]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_47,plain,
% 6.54/1.43      ( v2_struct_0(sK0) != iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_45,negated_conjecture,
% 6.54/1.43      ( v2_pre_topc(sK0) ),
% 6.54/1.43      inference(cnf_transformation,[],[f87]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_48,plain,
% 6.54/1.43      ( v2_pre_topc(sK0) = iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_44,negated_conjecture,
% 6.54/1.43      ( l1_pre_topc(sK0) ),
% 6.54/1.43      inference(cnf_transformation,[],[f88]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_49,plain,
% 6.54/1.43      ( l1_pre_topc(sK0) = iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_50,plain,
% 6.54/1.43      ( v2_struct_0(sK1) != iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_42,negated_conjecture,
% 6.54/1.43      ( v2_pre_topc(sK1) ),
% 6.54/1.43      inference(cnf_transformation,[],[f90]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_51,plain,
% 6.54/1.43      ( v2_pre_topc(sK1) = iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_52,plain,
% 6.54/1.43      ( l1_pre_topc(sK1) = iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_57,plain,
% 6.54/1.43      ( v1_funct_1(sK4) = iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_58,plain,
% 6.54/1.43      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_6820,plain,
% 6.54/1.43      ( m1_pre_topc(X0_61,sK0) != iProver_top
% 6.54/1.43      | k2_tmap_1(sK0,sK1,sK4,X0_61) = k7_relat_1(sK4,u1_struct_0(X0_61)) ),
% 6.54/1.43      inference(global_propositional_subsumption,
% 6.54/1.43                [status(thm)],
% 6.54/1.43                [c_4755,c_47,c_48,c_49,c_50,c_51,c_52,c_57,c_58]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_6821,plain,
% 6.54/1.43      ( k2_tmap_1(sK0,sK1,sK4,X0_61) = k7_relat_1(sK4,u1_struct_0(X0_61))
% 6.54/1.43      | m1_pre_topc(X0_61,sK0) != iProver_top ),
% 6.54/1.43      inference(renaming,[status(thm)],[c_6820]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_6829,plain,
% 6.54/1.43      ( k2_tmap_1(sK0,sK1,sK4,sK0) = k7_relat_1(sK4,u1_struct_0(sK0)) ),
% 6.54/1.43      inference(superposition,[status(thm)],[c_2029,c_6821]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_4,plain,
% 6.54/1.43      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v4_relat_1(X0,X1) ),
% 6.54/1.43      inference(cnf_transformation,[],[f66]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1,plain,
% 6.54/1.43      ( r1_tarski(k1_relat_1(X0),X1) | ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) ),
% 6.54/1.43      inference(cnf_transformation,[],[f62]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_593,plain,
% 6.54/1.43      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.54/1.43      | r1_tarski(k1_relat_1(X0),X1)
% 6.54/1.43      | ~ v1_relat_1(X0) ),
% 6.54/1.43      inference(resolution,[status(thm)],[c_4,c_1]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_3,plain,
% 6.54/1.43      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 6.54/1.43      inference(cnf_transformation,[],[f65]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_597,plain,
% 6.54/1.43      ( r1_tarski(k1_relat_1(X0),X1)
% 6.54/1.43      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 6.54/1.43      inference(global_propositional_subsumption,[status(thm)],[c_593,c_3]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_598,plain,
% 6.54/1.43      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.54/1.43      | r1_tarski(k1_relat_1(X0),X1) ),
% 6.54/1.43      inference(renaming,[status(thm)],[c_597]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2,plain,
% 6.54/1.43      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 6.54/1.43      | ~ v1_relat_1(X0)
% 6.54/1.43      | k7_relat_1(X0,X1) = X0 ),
% 6.54/1.43      inference(cnf_transformation,[],[f64]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_614,plain,
% 6.54/1.43      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.54/1.43      | ~ v1_relat_1(X0)
% 6.54/1.43      | k7_relat_1(X0,X1) = X0 ),
% 6.54/1.43      inference(resolution,[status(thm)],[c_598,c_2]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_618,plain,
% 6.54/1.43      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.54/1.43      | k7_relat_1(X0,X1) = X0 ),
% 6.54/1.43      inference(global_propositional_subsumption,[status(thm)],[c_614,c_3]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_984,plain,
% 6.54/1.43      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
% 6.54/1.43      | k7_relat_1(X0_57,X0_60) = X0_57 ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_618]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2011,plain,
% 6.54/1.43      ( k7_relat_1(X0_57,X0_60) = X0_57
% 6.54/1.43      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) != iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_984]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_6362,plain,
% 6.54/1.43      ( k7_relat_1(sK4,u1_struct_0(sK0)) = sK4 ),
% 6.54/1.43      inference(superposition,[status(thm)],[c_2050,c_2011]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_6831,plain,
% 6.54/1.43      ( k2_tmap_1(sK0,sK1,sK4,sK0) = sK4 ),
% 6.54/1.43      inference(light_normalisation,[status(thm)],[c_6829,c_6362]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_39,negated_conjecture,
% 6.54/1.43      ( m1_pre_topc(sK2,sK0) ),
% 6.54/1.43      inference(cnf_transformation,[],[f93]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_992,negated_conjecture,
% 6.54/1.43      ( m1_pre_topc(sK2,sK0) ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_39]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2003,plain,
% 6.54/1.43      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_992]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_6828,plain,
% 6.54/1.43      ( k2_tmap_1(sK0,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 6.54/1.43      inference(superposition,[status(thm)],[c_2003,c_6821]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_22,plain,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k2_tmap_1(X2,X1,X4,X3)),k2_tmap_1(X2,X1,X4,X0))
% 6.54/1.43      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
% 6.54/1.43      | ~ m1_pre_topc(X3,X2)
% 6.54/1.43      | ~ m1_pre_topc(X0,X2)
% 6.54/1.43      | ~ m1_pre_topc(X0,X3)
% 6.54/1.43      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 6.54/1.43      | ~ v2_pre_topc(X1)
% 6.54/1.43      | ~ v2_pre_topc(X2)
% 6.54/1.43      | v2_struct_0(X2)
% 6.54/1.43      | v2_struct_0(X1)
% 6.54/1.43      | v2_struct_0(X0)
% 6.54/1.43      | v2_struct_0(X3)
% 6.54/1.43      | ~ l1_pre_topc(X2)
% 6.54/1.43      | ~ l1_pre_topc(X1)
% 6.54/1.43      | ~ v1_funct_1(X4) ),
% 6.54/1.43      inference(cnf_transformation,[],[f84]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1008,plain,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(X0_61),u1_struct_0(X1_61),k3_tmap_1(X2_61,X1_61,X3_61,X0_61,k2_tmap_1(X2_61,X1_61,X0_57,X3_61)),k2_tmap_1(X2_61,X1_61,X0_57,X0_61))
% 6.54/1.43      | ~ v1_funct_2(X0_57,u1_struct_0(X2_61),u1_struct_0(X1_61))
% 6.54/1.43      | ~ m1_pre_topc(X3_61,X2_61)
% 6.54/1.43      | ~ m1_pre_topc(X0_61,X2_61)
% 6.54/1.43      | ~ m1_pre_topc(X0_61,X3_61)
% 6.54/1.43      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_61),u1_struct_0(X1_61))))
% 6.54/1.43      | ~ v2_pre_topc(X1_61)
% 6.54/1.43      | ~ v2_pre_topc(X2_61)
% 6.54/1.43      | v2_struct_0(X2_61)
% 6.54/1.43      | v2_struct_0(X1_61)
% 6.54/1.43      | v2_struct_0(X0_61)
% 6.54/1.43      | v2_struct_0(X3_61)
% 6.54/1.43      | ~ l1_pre_topc(X1_61)
% 6.54/1.43      | ~ l1_pre_topc(X2_61)
% 6.54/1.43      | ~ v1_funct_1(X0_57) ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_22]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1988,plain,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(X0_61),u1_struct_0(X1_61),k3_tmap_1(X2_61,X1_61,X3_61,X0_61,k2_tmap_1(X2_61,X1_61,X0_57,X3_61)),k2_tmap_1(X2_61,X1_61,X0_57,X0_61)) = iProver_top
% 6.54/1.43      | v1_funct_2(X0_57,u1_struct_0(X2_61),u1_struct_0(X1_61)) != iProver_top
% 6.54/1.43      | m1_pre_topc(X3_61,X2_61) != iProver_top
% 6.54/1.43      | m1_pre_topc(X0_61,X2_61) != iProver_top
% 6.54/1.43      | m1_pre_topc(X0_61,X3_61) != iProver_top
% 6.54/1.43      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_61),u1_struct_0(X1_61)))) != iProver_top
% 6.54/1.43      | v2_pre_topc(X1_61) != iProver_top
% 6.54/1.43      | v2_pre_topc(X2_61) != iProver_top
% 6.54/1.43      | v2_struct_0(X2_61) = iProver_top
% 6.54/1.43      | v2_struct_0(X1_61) = iProver_top
% 6.54/1.43      | v2_struct_0(X0_61) = iProver_top
% 6.54/1.43      | v2_struct_0(X3_61) = iProver_top
% 6.54/1.43      | l1_pre_topc(X1_61) != iProver_top
% 6.54/1.43      | l1_pre_topc(X2_61) != iProver_top
% 6.54/1.43      | v1_funct_1(X0_57) != iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_1008]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_23,plain,
% 6.54/1.43      ( ~ m1_pre_topc(X0,X1)
% 6.54/1.43      | ~ m1_pre_topc(X2,X0)
% 6.54/1.43      | m1_pre_topc(X2,X1)
% 6.54/1.43      | ~ v2_pre_topc(X1)
% 6.54/1.43      | ~ l1_pre_topc(X1) ),
% 6.54/1.43      inference(cnf_transformation,[],[f85]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1007,plain,
% 6.54/1.43      ( ~ m1_pre_topc(X0_61,X1_61)
% 6.54/1.43      | ~ m1_pre_topc(X2_61,X0_61)
% 6.54/1.43      | m1_pre_topc(X2_61,X1_61)
% 6.54/1.43      | ~ v2_pre_topc(X1_61)
% 6.54/1.43      | ~ l1_pre_topc(X1_61) ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_23]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1989,plain,
% 6.54/1.43      ( m1_pre_topc(X0_61,X1_61) != iProver_top
% 6.54/1.43      | m1_pre_topc(X2_61,X0_61) != iProver_top
% 6.54/1.43      | m1_pre_topc(X2_61,X1_61) = iProver_top
% 6.54/1.43      | v2_pre_topc(X1_61) != iProver_top
% 6.54/1.43      | l1_pre_topc(X1_61) != iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_1007]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2278,plain,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(X0_61),u1_struct_0(X1_61),k3_tmap_1(X2_61,X1_61,X3_61,X0_61,k2_tmap_1(X2_61,X1_61,X0_57,X3_61)),k2_tmap_1(X2_61,X1_61,X0_57,X0_61)) = iProver_top
% 6.54/1.43      | v1_funct_2(X0_57,u1_struct_0(X2_61),u1_struct_0(X1_61)) != iProver_top
% 6.54/1.43      | m1_pre_topc(X3_61,X2_61) != iProver_top
% 6.54/1.43      | m1_pre_topc(X0_61,X3_61) != iProver_top
% 6.54/1.43      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_61),u1_struct_0(X1_61)))) != iProver_top
% 6.54/1.43      | v2_pre_topc(X1_61) != iProver_top
% 6.54/1.43      | v2_pre_topc(X2_61) != iProver_top
% 6.54/1.43      | v2_struct_0(X2_61) = iProver_top
% 6.54/1.43      | v2_struct_0(X1_61) = iProver_top
% 6.54/1.43      | v2_struct_0(X0_61) = iProver_top
% 6.54/1.43      | v2_struct_0(X3_61) = iProver_top
% 6.54/1.43      | l1_pre_topc(X1_61) != iProver_top
% 6.54/1.43      | l1_pre_topc(X2_61) != iProver_top
% 6.54/1.43      | v1_funct_1(X0_57) != iProver_top ),
% 6.54/1.43      inference(forward_subsumption_resolution,[status(thm)],[c_1988,c_1989]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_6999,plain,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_61,sK2,k2_tmap_1(sK0,sK1,sK4,X0_61)),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
% 6.54/1.43      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 6.54/1.43      | m1_pre_topc(X0_61,sK0) != iProver_top
% 6.54/1.43      | m1_pre_topc(sK2,X0_61) != iProver_top
% 6.54/1.43      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 6.54/1.43      | v2_pre_topc(sK0) != iProver_top
% 6.54/1.43      | v2_pre_topc(sK1) != iProver_top
% 6.54/1.43      | v2_struct_0(X0_61) = iProver_top
% 6.54/1.43      | v2_struct_0(sK0) = iProver_top
% 6.54/1.43      | v2_struct_0(sK1) = iProver_top
% 6.54/1.43      | v2_struct_0(sK2) = iProver_top
% 6.54/1.43      | l1_pre_topc(sK0) != iProver_top
% 6.54/1.43      | l1_pre_topc(sK1) != iProver_top
% 6.54/1.43      | v1_funct_1(sK4) != iProver_top ),
% 6.54/1.43      inference(superposition,[status(thm)],[c_6828,c_2278]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_40,negated_conjecture,
% 6.54/1.43      ( ~ v2_struct_0(sK2) ),
% 6.54/1.43      inference(cnf_transformation,[],[f92]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_53,plain,
% 6.54/1.43      ( v2_struct_0(sK2) != iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_59,plain,
% 6.54/1.43      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_8681,plain,
% 6.54/1.43      ( m1_pre_topc(sK2,X0_61) != iProver_top
% 6.54/1.43      | m1_pre_topc(X0_61,sK0) != iProver_top
% 6.54/1.43      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_61,sK2,k2_tmap_1(sK0,sK1,sK4,X0_61)),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
% 6.54/1.43      | v2_struct_0(X0_61) = iProver_top ),
% 6.54/1.43      inference(global_propositional_subsumption,
% 6.54/1.43                [status(thm)],
% 6.54/1.43                [c_6999,c_47,c_48,c_49,c_50,c_51,c_52,c_53,c_57,c_58,c_59]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_8682,plain,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_61,sK2,k2_tmap_1(sK0,sK1,sK4,X0_61)),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
% 6.54/1.43      | m1_pre_topc(X0_61,sK0) != iProver_top
% 6.54/1.43      | m1_pre_topc(sK2,X0_61) != iProver_top
% 6.54/1.43      | v2_struct_0(X0_61) = iProver_top ),
% 6.54/1.43      inference(renaming,[status(thm)],[c_8681]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_16,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 6.54/1.43      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 6.54/1.43      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 6.54/1.43      | ~ l1_struct_0(X1)
% 6.54/1.43      | ~ l1_struct_0(X2)
% 6.54/1.43      | ~ l1_struct_0(X3)
% 6.54/1.43      | ~ v1_funct_1(X0) ),
% 6.54/1.43      inference(cnf_transformation,[],[f80]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1014,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61))
% 6.54/1.43      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
% 6.54/1.43      | m1_subset_1(k2_tmap_1(X0_61,X1_61,X0_57,X2_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_61),u1_struct_0(X1_61))))
% 6.54/1.43      | ~ l1_struct_0(X1_61)
% 6.54/1.43      | ~ l1_struct_0(X2_61)
% 6.54/1.43      | ~ l1_struct_0(X0_61)
% 6.54/1.43      | ~ v1_funct_1(X0_57) ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_16]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1982,plain,
% 6.54/1.43      ( v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61)) != iProver_top
% 6.54/1.43      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61)))) != iProver_top
% 6.54/1.43      | m1_subset_1(k2_tmap_1(X0_61,X1_61,X0_57,X2_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_61),u1_struct_0(X1_61)))) = iProver_top
% 6.54/1.43      | l1_struct_0(X1_61) != iProver_top
% 6.54/1.43      | l1_struct_0(X2_61) != iProver_top
% 6.54/1.43      | l1_struct_0(X0_61) != iProver_top
% 6.54/1.43      | v1_funct_1(X0_57) != iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_1014]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_6855,plain,
% 6.54/1.43      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 6.54/1.43      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 6.54/1.43      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 6.54/1.43      | l1_struct_0(sK0) != iProver_top
% 6.54/1.43      | l1_struct_0(sK1) != iProver_top
% 6.54/1.43      | l1_struct_0(sK2) != iProver_top
% 6.54/1.43      | v1_funct_1(sK4) != iProver_top ),
% 6.54/1.43      inference(superposition,[status(thm)],[c_6828,c_1982]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_104,plain,
% 6.54/1.43      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_106,plain,
% 6.54/1.43      ( l1_pre_topc(sK1) != iProver_top | l1_struct_0(sK1) = iProver_top ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_104]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1017,plain,
% 6.54/1.43      ( ~ l1_pre_topc(X0_61) | l1_struct_0(X0_61) ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_10]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2750,plain,
% 6.54/1.43      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_1017]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2751,plain,
% 6.54/1.43      ( l1_pre_topc(sK2) != iProver_top | l1_struct_0(sK2) = iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_2750]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2753,plain,
% 6.54/1.43      ( ~ l1_pre_topc(sK0) | l1_struct_0(sK0) ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_1017]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2754,plain,
% 6.54/1.43      ( l1_pre_topc(sK0) != iProver_top | l1_struct_0(sK0) = iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_2753]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_11,plain,
% 6.54/1.43      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 6.54/1.43      inference(cnf_transformation,[],[f73]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1016,plain,
% 6.54/1.43      ( ~ m1_pre_topc(X0_61,X1_61)
% 6.54/1.43      | ~ l1_pre_topc(X1_61)
% 6.54/1.43      | l1_pre_topc(X0_61) ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_11]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1980,plain,
% 6.54/1.43      ( m1_pre_topc(X0_61,X1_61) != iProver_top
% 6.54/1.43      | l1_pre_topc(X1_61) != iProver_top
% 6.54/1.43      | l1_pre_topc(X0_61) = iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_1016]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_3087,plain,
% 6.54/1.43      ( l1_pre_topc(sK0) != iProver_top | l1_pre_topc(sK2) = iProver_top ),
% 6.54/1.43      inference(superposition,[status(thm)],[c_2003,c_1980]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_7757,plain,
% 6.54/1.43      ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 6.54/1.43      inference(global_propositional_subsumption,
% 6.54/1.43                [status(thm)],
% 6.54/1.43                [c_6855,c_49,c_52,c_57,c_58,c_59,c_106,c_2751,c_2754,c_3087]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_9,plain,
% 6.54/1.43      ( ~ r2_funct_2(X0,X1,X2,X3)
% 6.54/1.43      | ~ v1_funct_2(X3,X0,X1)
% 6.54/1.43      | ~ v1_funct_2(X2,X0,X1)
% 6.54/1.43      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.54/1.43      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.54/1.43      | ~ v1_funct_1(X2)
% 6.54/1.43      | ~ v1_funct_1(X3)
% 6.54/1.43      | X3 = X2 ),
% 6.54/1.43      inference(cnf_transformation,[],[f70]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1018,plain,
% 6.54/1.43      ( ~ r2_funct_2(X0_60,X1_60,X0_57,X1_57)
% 6.54/1.43      | ~ v1_funct_2(X1_57,X0_60,X1_60)
% 6.54/1.43      | ~ v1_funct_2(X0_57,X0_60,X1_60)
% 6.54/1.43      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
% 6.54/1.43      | ~ m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
% 6.54/1.43      | ~ v1_funct_1(X0_57)
% 6.54/1.43      | ~ v1_funct_1(X1_57)
% 6.54/1.43      | X1_57 = X0_57 ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_9]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1978,plain,
% 6.54/1.43      ( X0_57 = X1_57
% 6.54/1.43      | r2_funct_2(X0_60,X1_60,X1_57,X0_57) != iProver_top
% 6.54/1.43      | v1_funct_2(X1_57,X0_60,X1_60) != iProver_top
% 6.54/1.43      | v1_funct_2(X0_57,X0_60,X1_60) != iProver_top
% 6.54/1.43      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) != iProver_top
% 6.54/1.43      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) != iProver_top
% 6.54/1.43      | v1_funct_1(X1_57) != iProver_top
% 6.54/1.43      | v1_funct_1(X0_57) != iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_1018]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_7764,plain,
% 6.54/1.43      ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_57
% 6.54/1.43      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_57,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 6.54/1.43      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 6.54/1.43      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 6.54/1.43      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 6.54/1.43      | v1_funct_1(X0_57) != iProver_top
% 6.54/1.43      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
% 6.54/1.43      inference(superposition,[status(thm)],[c_7757,c_1978]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_17,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 6.54/1.43      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 6.54/1.43      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 6.54/1.43      | ~ l1_struct_0(X1)
% 6.54/1.43      | ~ l1_struct_0(X2)
% 6.54/1.43      | ~ l1_struct_0(X3)
% 6.54/1.43      | ~ v1_funct_1(X0) ),
% 6.54/1.43      inference(cnf_transformation,[],[f79]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1013,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61))
% 6.54/1.43      | v1_funct_2(k2_tmap_1(X0_61,X1_61,X0_57,X2_61),u1_struct_0(X2_61),u1_struct_0(X1_61))
% 6.54/1.43      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
% 6.54/1.43      | ~ l1_struct_0(X1_61)
% 6.54/1.43      | ~ l1_struct_0(X2_61)
% 6.54/1.43      | ~ l1_struct_0(X0_61)
% 6.54/1.43      | ~ v1_funct_1(X0_57) ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_17]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1983,plain,
% 6.54/1.43      ( v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61)) != iProver_top
% 6.54/1.43      | v1_funct_2(k2_tmap_1(X0_61,X1_61,X0_57,X2_61),u1_struct_0(X2_61),u1_struct_0(X1_61)) = iProver_top
% 6.54/1.43      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61)))) != iProver_top
% 6.54/1.43      | l1_struct_0(X1_61) != iProver_top
% 6.54/1.43      | l1_struct_0(X2_61) != iProver_top
% 6.54/1.43      | l1_struct_0(X0_61) != iProver_top
% 6.54/1.43      | v1_funct_1(X0_57) != iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_1013]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_6856,plain,
% 6.54/1.43      ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 6.54/1.43      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 6.54/1.43      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 6.54/1.43      | l1_struct_0(sK0) != iProver_top
% 6.54/1.43      | l1_struct_0(sK1) != iProver_top
% 6.54/1.43      | l1_struct_0(sK2) != iProver_top
% 6.54/1.43      | v1_funct_1(sK4) != iProver_top ),
% 6.54/1.43      inference(superposition,[status(thm)],[c_6828,c_1983]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_11945,plain,
% 6.54/1.43      ( v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 6.54/1.43      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_57,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 6.54/1.43      | k7_relat_1(sK4,u1_struct_0(sK2)) = X0_57
% 6.54/1.43      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 6.54/1.43      | v1_funct_1(X0_57) != iProver_top
% 6.54/1.43      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
% 6.54/1.43      inference(global_propositional_subsumption,
% 6.54/1.43                [status(thm)],
% 6.54/1.43                [c_7764,c_49,c_52,c_57,c_58,c_59,c_106,c_2751,c_2754,c_3087,
% 6.54/1.43                 c_6856]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_11946,plain,
% 6.54/1.43      ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_57
% 6.54/1.43      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_57,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 6.54/1.43      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 6.54/1.43      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 6.54/1.43      | v1_funct_1(X0_57) != iProver_top
% 6.54/1.43      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
% 6.54/1.43      inference(renaming,[status(thm)],[c_11945]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_6,plain,
% 6.54/1.43      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.54/1.43      | ~ v1_funct_1(X0)
% 6.54/1.43      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 6.54/1.43      inference(cnf_transformation,[],[f67]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1021,plain,
% 6.54/1.43      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
% 6.54/1.43      | ~ v1_funct_1(X0_57)
% 6.54/1.43      | v1_funct_1(k2_partfun1(X0_60,X1_60,X0_57,X2_60)) ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_6]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1975,plain,
% 6.54/1.43      ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) != iProver_top
% 6.54/1.43      | v1_funct_1(X0_57) != iProver_top
% 6.54/1.43      | v1_funct_1(k2_partfun1(X0_60,X1_60,X0_57,X2_60)) = iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_1021]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2957,plain,
% 6.54/1.43      ( v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_60)) = iProver_top
% 6.54/1.43      | v1_funct_1(sK4) != iProver_top ),
% 6.54/1.43      inference(superposition,[status(thm)],[c_2050,c_1975]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2416,plain,
% 6.54/1.43      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 6.54/1.43      | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_60))
% 6.54/1.43      | ~ v1_funct_1(sK4) ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_1021]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2417,plain,
% 6.54/1.43      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 6.54/1.43      | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_60)) = iProver_top
% 6.54/1.43      | v1_funct_1(sK4) != iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_2416]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_3611,plain,
% 6.54/1.43      ( v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_60)) = iProver_top ),
% 6.54/1.43      inference(global_propositional_subsumption,
% 6.54/1.43                [status(thm)],
% 6.54/1.43                [c_2957,c_57,c_59,c_2417]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_3763,plain,
% 6.54/1.43      ( v1_funct_1(k7_relat_1(sK4,X0_60)) = iProver_top ),
% 6.54/1.43      inference(demodulation,[status(thm)],[c_3759,c_3611]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_11957,plain,
% 6.54/1.43      ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_57
% 6.54/1.43      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_57,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 6.54/1.43      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 6.54/1.43      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 6.54/1.43      | v1_funct_1(X0_57) != iProver_top ),
% 6.54/1.43      inference(forward_subsumption_resolution,[status(thm)],[c_11946,c_3763]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_11961,plain,
% 6.54/1.43      ( k3_tmap_1(sK0,sK1,X0_61,sK2,k2_tmap_1(sK0,sK1,sK4,X0_61)) = k7_relat_1(sK4,u1_struct_0(sK2))
% 6.54/1.43      | v1_funct_2(k3_tmap_1(sK0,sK1,X0_61,sK2,k2_tmap_1(sK0,sK1,sK4,X0_61)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 6.54/1.43      | m1_pre_topc(X0_61,sK0) != iProver_top
% 6.54/1.43      | m1_pre_topc(sK2,X0_61) != iProver_top
% 6.54/1.43      | m1_subset_1(k3_tmap_1(sK0,sK1,X0_61,sK2,k2_tmap_1(sK0,sK1,sK4,X0_61)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 6.54/1.43      | v2_struct_0(X0_61) = iProver_top
% 6.54/1.43      | v1_funct_1(k3_tmap_1(sK0,sK1,X0_61,sK2,k2_tmap_1(sK0,sK1,sK4,X0_61))) != iProver_top ),
% 6.54/1.43      inference(superposition,[status(thm)],[c_8682,c_11957]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_14721,plain,
% 6.54/1.43      ( k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0)) = k7_relat_1(sK4,u1_struct_0(sK2))
% 6.54/1.43      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 6.54/1.43      | m1_pre_topc(sK0,sK0) != iProver_top
% 6.54/1.43      | m1_pre_topc(sK2,sK0) != iProver_top
% 6.54/1.43      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 6.54/1.43      | v2_struct_0(sK0) = iProver_top
% 6.54/1.43      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0))) != iProver_top ),
% 6.54/1.43      inference(superposition,[status(thm)],[c_6831,c_11961]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_14729,plain,
% 6.54/1.43      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
% 6.54/1.43      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 6.54/1.43      | m1_pre_topc(sK0,sK0) != iProver_top
% 6.54/1.43      | m1_pre_topc(sK2,sK0) != iProver_top
% 6.54/1.43      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 6.54/1.43      | v2_struct_0(sK0) = iProver_top
% 6.54/1.43      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
% 6.54/1.43      inference(light_normalisation,[status(thm)],[c_14721,c_6831]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_54,plain,
% 6.54/1.43      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_20,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 6.54/1.43      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 6.54/1.43      | ~ m1_pre_topc(X4,X3)
% 6.54/1.43      | ~ m1_pre_topc(X1,X3)
% 6.54/1.43      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 6.54/1.43      | ~ v2_pre_topc(X2)
% 6.54/1.43      | ~ v2_pre_topc(X3)
% 6.54/1.43      | v2_struct_0(X3)
% 6.54/1.43      | v2_struct_0(X2)
% 6.54/1.43      | ~ l1_pre_topc(X3)
% 6.54/1.43      | ~ l1_pre_topc(X2)
% 6.54/1.43      | ~ v1_funct_1(X0) ),
% 6.54/1.43      inference(cnf_transformation,[],[f82]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1010,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61))
% 6.54/1.43      | v1_funct_2(k3_tmap_1(X2_61,X1_61,X0_61,X3_61,X0_57),u1_struct_0(X3_61),u1_struct_0(X1_61))
% 6.54/1.43      | ~ m1_pre_topc(X3_61,X2_61)
% 6.54/1.43      | ~ m1_pre_topc(X0_61,X2_61)
% 6.54/1.43      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
% 6.54/1.43      | ~ v2_pre_topc(X1_61)
% 6.54/1.43      | ~ v2_pre_topc(X2_61)
% 6.54/1.43      | v2_struct_0(X2_61)
% 6.54/1.43      | v2_struct_0(X1_61)
% 6.54/1.43      | ~ l1_pre_topc(X1_61)
% 6.54/1.43      | ~ l1_pre_topc(X2_61)
% 6.54/1.43      | ~ v1_funct_1(X0_57) ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_20]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2581,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61))
% 6.54/1.43      | v1_funct_2(k3_tmap_1(sK0,X1_61,X0_61,sK2,X0_57),u1_struct_0(sK2),u1_struct_0(X1_61))
% 6.54/1.43      | ~ m1_pre_topc(X0_61,sK0)
% 6.54/1.43      | ~ m1_pre_topc(sK2,sK0)
% 6.54/1.43      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
% 6.54/1.43      | ~ v2_pre_topc(X1_61)
% 6.54/1.43      | ~ v2_pre_topc(sK0)
% 6.54/1.43      | v2_struct_0(X1_61)
% 6.54/1.43      | v2_struct_0(sK0)
% 6.54/1.43      | ~ l1_pre_topc(X1_61)
% 6.54/1.43      | ~ l1_pre_topc(sK0)
% 6.54/1.43      | ~ v1_funct_1(X0_57) ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_1010]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_3205,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0_57,u1_struct_0(sK0),u1_struct_0(X0_61))
% 6.54/1.43      | v1_funct_2(k3_tmap_1(sK0,X0_61,sK0,sK2,X0_57),u1_struct_0(sK2),u1_struct_0(X0_61))
% 6.54/1.43      | ~ m1_pre_topc(sK0,sK0)
% 6.54/1.43      | ~ m1_pre_topc(sK2,sK0)
% 6.54/1.43      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_61))))
% 6.54/1.43      | ~ v2_pre_topc(X0_61)
% 6.54/1.43      | ~ v2_pre_topc(sK0)
% 6.54/1.43      | v2_struct_0(X0_61)
% 6.54/1.43      | v2_struct_0(sK0)
% 6.54/1.43      | ~ l1_pre_topc(X0_61)
% 6.54/1.43      | ~ l1_pre_topc(sK0)
% 6.54/1.43      | ~ v1_funct_1(X0_57) ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_2581]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_4493,plain,
% 6.54/1.43      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
% 6.54/1.43      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 6.54/1.43      | ~ m1_pre_topc(sK0,sK0)
% 6.54/1.43      | ~ m1_pre_topc(sK2,sK0)
% 6.54/1.43      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 6.54/1.43      | ~ v2_pre_topc(sK0)
% 6.54/1.43      | ~ v2_pre_topc(sK1)
% 6.54/1.43      | v2_struct_0(sK0)
% 6.54/1.43      | v2_struct_0(sK1)
% 6.54/1.43      | ~ l1_pre_topc(sK0)
% 6.54/1.43      | ~ l1_pre_topc(sK1)
% 6.54/1.43      | ~ v1_funct_1(sK4) ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_3205]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_4494,plain,
% 6.54/1.43      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 6.54/1.43      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 6.54/1.43      | m1_pre_topc(sK0,sK0) != iProver_top
% 6.54/1.43      | m1_pre_topc(sK2,sK0) != iProver_top
% 6.54/1.43      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 6.54/1.43      | v2_pre_topc(sK0) != iProver_top
% 6.54/1.43      | v2_pre_topc(sK1) != iProver_top
% 6.54/1.43      | v2_struct_0(sK0) = iProver_top
% 6.54/1.43      | v2_struct_0(sK1) = iProver_top
% 6.54/1.43      | l1_pre_topc(sK0) != iProver_top
% 6.54/1.43      | l1_pre_topc(sK1) != iProver_top
% 6.54/1.43      | v1_funct_1(sK4) != iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_4493]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_21,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 6.54/1.43      | ~ m1_pre_topc(X3,X4)
% 6.54/1.43      | ~ m1_pre_topc(X1,X4)
% 6.54/1.43      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 6.54/1.43      | ~ v2_pre_topc(X2)
% 6.54/1.43      | ~ v2_pre_topc(X4)
% 6.54/1.43      | v2_struct_0(X4)
% 6.54/1.43      | v2_struct_0(X2)
% 6.54/1.43      | ~ l1_pre_topc(X4)
% 6.54/1.43      | ~ l1_pre_topc(X2)
% 6.54/1.43      | ~ v1_funct_1(X0)
% 6.54/1.43      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 6.54/1.43      inference(cnf_transformation,[],[f81]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1009,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61))
% 6.54/1.43      | ~ m1_pre_topc(X0_61,X2_61)
% 6.54/1.43      | ~ m1_pre_topc(X3_61,X2_61)
% 6.54/1.43      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
% 6.54/1.43      | ~ v2_pre_topc(X1_61)
% 6.54/1.43      | ~ v2_pre_topc(X2_61)
% 6.54/1.43      | v2_struct_0(X1_61)
% 6.54/1.43      | v2_struct_0(X2_61)
% 6.54/1.43      | ~ l1_pre_topc(X1_61)
% 6.54/1.43      | ~ l1_pre_topc(X2_61)
% 6.54/1.43      | ~ v1_funct_1(X0_57)
% 6.54/1.43      | v1_funct_1(k3_tmap_1(X2_61,X1_61,X0_61,X3_61,X0_57)) ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_21]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_3183,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0_57,u1_struct_0(sK0),u1_struct_0(X0_61))
% 6.54/1.43      | ~ m1_pre_topc(X1_61,X2_61)
% 6.54/1.43      | ~ m1_pre_topc(sK0,X2_61)
% 6.54/1.43      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_61))))
% 6.54/1.43      | ~ v2_pre_topc(X2_61)
% 6.54/1.43      | ~ v2_pre_topc(X0_61)
% 6.54/1.43      | v2_struct_0(X2_61)
% 6.54/1.43      | v2_struct_0(X0_61)
% 6.54/1.43      | ~ l1_pre_topc(X2_61)
% 6.54/1.43      | ~ l1_pre_topc(X0_61)
% 6.54/1.43      | ~ v1_funct_1(X0_57)
% 6.54/1.43      | v1_funct_1(k3_tmap_1(X2_61,X0_61,sK0,X1_61,X0_57)) ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_1009]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_5037,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0_57,u1_struct_0(sK0),u1_struct_0(X0_61))
% 6.54/1.43      | ~ m1_pre_topc(X1_61,sK0)
% 6.54/1.43      | ~ m1_pre_topc(sK0,sK0)
% 6.54/1.43      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_61))))
% 6.54/1.43      | ~ v2_pre_topc(X0_61)
% 6.54/1.43      | ~ v2_pre_topc(sK0)
% 6.54/1.43      | v2_struct_0(X0_61)
% 6.54/1.43      | v2_struct_0(sK0)
% 6.54/1.43      | ~ l1_pre_topc(X0_61)
% 6.54/1.43      | ~ l1_pre_topc(sK0)
% 6.54/1.43      | ~ v1_funct_1(X0_57)
% 6.54/1.43      | v1_funct_1(k3_tmap_1(sK0,X0_61,sK0,X1_61,X0_57)) ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_3183]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_9162,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0_57,u1_struct_0(sK0),u1_struct_0(X0_61))
% 6.54/1.43      | ~ m1_pre_topc(sK0,sK0)
% 6.54/1.43      | ~ m1_pre_topc(sK2,sK0)
% 6.54/1.43      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_61))))
% 6.54/1.43      | ~ v2_pre_topc(X0_61)
% 6.54/1.43      | ~ v2_pre_topc(sK0)
% 6.54/1.43      | v2_struct_0(X0_61)
% 6.54/1.43      | v2_struct_0(sK0)
% 6.54/1.43      | ~ l1_pre_topc(X0_61)
% 6.54/1.43      | ~ l1_pre_topc(sK0)
% 6.54/1.43      | ~ v1_funct_1(X0_57)
% 6.54/1.43      | v1_funct_1(k3_tmap_1(sK0,X0_61,sK0,sK2,X0_57)) ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_5037]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_11166,plain,
% 6.54/1.43      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 6.54/1.43      | ~ m1_pre_topc(sK0,sK0)
% 6.54/1.43      | ~ m1_pre_topc(sK2,sK0)
% 6.54/1.43      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 6.54/1.43      | ~ v2_pre_topc(sK0)
% 6.54/1.43      | ~ v2_pre_topc(sK1)
% 6.54/1.43      | v2_struct_0(sK0)
% 6.54/1.43      | v2_struct_0(sK1)
% 6.54/1.43      | ~ l1_pre_topc(sK0)
% 6.54/1.43      | ~ l1_pre_topc(sK1)
% 6.54/1.43      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
% 6.54/1.43      | ~ v1_funct_1(sK4) ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_9162]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_11167,plain,
% 6.54/1.43      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 6.54/1.43      | m1_pre_topc(sK0,sK0) != iProver_top
% 6.54/1.43      | m1_pre_topc(sK2,sK0) != iProver_top
% 6.54/1.43      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 6.54/1.43      | v2_pre_topc(sK0) != iProver_top
% 6.54/1.43      | v2_pre_topc(sK1) != iProver_top
% 6.54/1.43      | v2_struct_0(sK0) = iProver_top
% 6.54/1.43      | v2_struct_0(sK1) = iProver_top
% 6.54/1.43      | l1_pre_topc(sK0) != iProver_top
% 6.54/1.43      | l1_pre_topc(sK1) != iProver_top
% 6.54/1.43      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) = iProver_top
% 6.54/1.43      | v1_funct_1(sK4) != iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_11166]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_19,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 6.54/1.43      | ~ m1_pre_topc(X3,X4)
% 6.54/1.43      | ~ m1_pre_topc(X1,X4)
% 6.54/1.43      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 6.54/1.43      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 6.54/1.43      | ~ v2_pre_topc(X2)
% 6.54/1.43      | ~ v2_pre_topc(X4)
% 6.54/1.43      | v2_struct_0(X4)
% 6.54/1.43      | v2_struct_0(X2)
% 6.54/1.43      | ~ l1_pre_topc(X4)
% 6.54/1.43      | ~ l1_pre_topc(X2)
% 6.54/1.43      | ~ v1_funct_1(X0) ),
% 6.54/1.43      inference(cnf_transformation,[],[f83]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1011,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0_57,u1_struct_0(X0_61),u1_struct_0(X1_61))
% 6.54/1.43      | ~ m1_pre_topc(X0_61,X2_61)
% 6.54/1.43      | ~ m1_pre_topc(X3_61,X2_61)
% 6.54/1.43      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
% 6.54/1.43      | m1_subset_1(k3_tmap_1(X2_61,X1_61,X0_61,X3_61,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_61),u1_struct_0(X1_61))))
% 6.54/1.43      | ~ v2_pre_topc(X1_61)
% 6.54/1.43      | ~ v2_pre_topc(X2_61)
% 6.54/1.43      | v2_struct_0(X1_61)
% 6.54/1.43      | v2_struct_0(X2_61)
% 6.54/1.43      | ~ l1_pre_topc(X1_61)
% 6.54/1.43      | ~ l1_pre_topc(X2_61)
% 6.54/1.43      | ~ v1_funct_1(X0_57) ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_19]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_3182,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0_57,u1_struct_0(sK0),u1_struct_0(X0_61))
% 6.54/1.43      | ~ m1_pre_topc(X1_61,X2_61)
% 6.54/1.43      | ~ m1_pre_topc(sK0,X2_61)
% 6.54/1.43      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_61))))
% 6.54/1.43      | m1_subset_1(k3_tmap_1(X2_61,X0_61,sK0,X1_61,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_61),u1_struct_0(X0_61))))
% 6.54/1.43      | ~ v2_pre_topc(X2_61)
% 6.54/1.43      | ~ v2_pre_topc(X0_61)
% 6.54/1.43      | v2_struct_0(X2_61)
% 6.54/1.43      | v2_struct_0(X0_61)
% 6.54/1.43      | ~ l1_pre_topc(X2_61)
% 6.54/1.43      | ~ l1_pre_topc(X0_61)
% 6.54/1.43      | ~ v1_funct_1(X0_57) ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_1011]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_5057,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0_57,u1_struct_0(sK0),u1_struct_0(X0_61))
% 6.54/1.43      | ~ m1_pre_topc(X1_61,sK0)
% 6.54/1.43      | ~ m1_pre_topc(sK0,sK0)
% 6.54/1.43      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_61))))
% 6.54/1.43      | m1_subset_1(k3_tmap_1(sK0,X0_61,sK0,X1_61,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_61),u1_struct_0(X0_61))))
% 6.54/1.43      | ~ v2_pre_topc(X0_61)
% 6.54/1.43      | ~ v2_pre_topc(sK0)
% 6.54/1.43      | v2_struct_0(X0_61)
% 6.54/1.43      | v2_struct_0(sK0)
% 6.54/1.43      | ~ l1_pre_topc(X0_61)
% 6.54/1.43      | ~ l1_pre_topc(sK0)
% 6.54/1.43      | ~ v1_funct_1(X0_57) ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_3182]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_9442,plain,
% 6.54/1.43      ( ~ v1_funct_2(X0_57,u1_struct_0(sK0),u1_struct_0(X0_61))
% 6.54/1.43      | ~ m1_pre_topc(sK0,sK0)
% 6.54/1.43      | ~ m1_pre_topc(sK2,sK0)
% 6.54/1.43      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_61))))
% 6.54/1.43      | m1_subset_1(k3_tmap_1(sK0,X0_61,sK0,sK2,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_61))))
% 6.54/1.43      | ~ v2_pre_topc(X0_61)
% 6.54/1.43      | ~ v2_pre_topc(sK0)
% 6.54/1.43      | v2_struct_0(X0_61)
% 6.54/1.43      | v2_struct_0(sK0)
% 6.54/1.43      | ~ l1_pre_topc(X0_61)
% 6.54/1.43      | ~ l1_pre_topc(sK0)
% 6.54/1.43      | ~ v1_funct_1(X0_57) ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_5057]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_11392,plain,
% 6.54/1.43      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 6.54/1.43      | ~ m1_pre_topc(sK0,sK0)
% 6.54/1.43      | ~ m1_pre_topc(sK2,sK0)
% 6.54/1.43      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 6.54/1.43      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 6.54/1.43      | ~ v2_pre_topc(sK0)
% 6.54/1.43      | ~ v2_pre_topc(sK1)
% 6.54/1.43      | v2_struct_0(sK0)
% 6.54/1.43      | v2_struct_0(sK1)
% 6.54/1.43      | ~ l1_pre_topc(sK0)
% 6.54/1.43      | ~ l1_pre_topc(sK1)
% 6.54/1.43      | ~ v1_funct_1(sK4) ),
% 6.54/1.43      inference(instantiation,[status(thm)],[c_9442]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_11393,plain,
% 6.54/1.43      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 6.54/1.43      | m1_pre_topc(sK0,sK0) != iProver_top
% 6.54/1.43      | m1_pre_topc(sK2,sK0) != iProver_top
% 6.54/1.43      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 6.54/1.43      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 6.54/1.43      | v2_pre_topc(sK0) != iProver_top
% 6.54/1.43      | v2_pre_topc(sK1) != iProver_top
% 6.54/1.43      | v2_struct_0(sK0) = iProver_top
% 6.54/1.43      | v2_struct_0(sK1) = iProver_top
% 6.54/1.43      | l1_pre_topc(sK0) != iProver_top
% 6.54/1.43      | l1_pre_topc(sK1) != iProver_top
% 6.54/1.43      | v1_funct_1(sK4) != iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_11392]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_8692,plain,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
% 6.54/1.43      | m1_pre_topc(sK0,sK0) != iProver_top
% 6.54/1.43      | m1_pre_topc(sK2,sK0) != iProver_top
% 6.54/1.43      | v2_struct_0(sK0) = iProver_top ),
% 6.54/1.43      inference(superposition,[status(thm)],[c_6831,c_8682]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_12988,plain,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top ),
% 6.54/1.43      inference(global_propositional_subsumption,
% 6.54/1.43                [status(thm)],
% 6.54/1.43                [c_8692,c_47,c_54,c_2029]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_12994,plain,
% 6.54/1.43      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
% 6.54/1.43      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 6.54/1.43      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 6.54/1.43      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
% 6.54/1.43      inference(superposition,[status(thm)],[c_12988,c_11957]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_14896,plain,
% 6.54/1.43      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 6.54/1.43      inference(global_propositional_subsumption,
% 6.54/1.43                [status(thm)],
% 6.54/1.43                [c_14729,c_47,c_48,c_49,c_50,c_51,c_52,c_54,c_57,c_58,c_59,
% 6.54/1.43                 c_2029,c_4494,c_11167,c_11393,c_12994]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_25,negated_conjecture,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 6.54/1.43      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 6.54/1.43      inference(cnf_transformation,[],[f107]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1005,negated_conjecture,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 6.54/1.43      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_25]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1991,plain,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) = iProver_top
% 6.54/1.43      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_1005]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2083,plain,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
% 6.54/1.43      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
% 6.54/1.43      inference(light_normalisation,[status(thm)],[c_1991,c_983,c_1004]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_6843,plain,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
% 6.54/1.43      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top ),
% 6.54/1.43      inference(demodulation,[status(thm)],[c_6828,c_2083]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_14901,plain,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top ),
% 6.54/1.43      inference(demodulation,[status(thm)],[c_14896,c_6843]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_24,negated_conjecture,
% 6.54/1.43      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 6.54/1.43      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 6.54/1.43      inference(cnf_transformation,[],[f108]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1006,negated_conjecture,
% 6.54/1.43      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 6.54/1.43      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 6.54/1.43      inference(subtyping,[status(esa)],[c_24]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_1990,plain,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) != iProver_top
% 6.54/1.43      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
% 6.54/1.43      inference(predicate_to_equality,[status(thm)],[c_1006]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_2088,plain,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
% 6.54/1.43      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
% 6.54/1.43      inference(light_normalisation,[status(thm)],[c_1990,c_983,c_1004]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_6844,plain,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
% 6.54/1.43      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top ),
% 6.54/1.43      inference(demodulation,[status(thm)],[c_6828,c_2088]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_14902,plain,
% 6.54/1.43      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top ),
% 6.54/1.43      inference(demodulation,[status(thm)],[c_14896,c_6844]) ).
% 6.54/1.43  
% 6.54/1.43  cnf(c_14906,plain,
% 6.54/1.43      ( $false ),
% 6.54/1.43      inference(forward_subsumption_resolution,[status(thm)],[c_14901,c_14902]) ).
% 6.54/1.43  
% 6.54/1.43  
% 6.54/1.43  % SZS output end CNFRefutation for theBenchmark.p
% 6.54/1.43  
% 6.54/1.43  ------                               Statistics
% 6.54/1.43  
% 6.54/1.43  ------ General
% 6.54/1.43  
% 6.54/1.43  abstr_ref_over_cycles:                  0
% 6.54/1.43  abstr_ref_under_cycles:                 0
% 6.54/1.43  gc_basic_clause_elim:                   0
% 6.54/1.43  forced_gc_time:                         0
% 6.54/1.43  parsing_time:                           0.011
% 6.54/1.43  unif_index_cands_time:                  0.
% 6.54/1.43  unif_index_add_time:                    0.
% 6.54/1.43  orderings_time:                         0.
% 6.54/1.43  out_proof_time:                         0.018
% 6.54/1.43  total_time:                             0.516
% 6.54/1.43  num_of_symbols:                         62
% 6.54/1.43  num_of_terms:                           15674
% 6.54/1.43  
% 6.54/1.43  ------ Preprocessing
% 6.54/1.43  
% 6.54/1.43  num_of_splits:                          0
% 6.54/1.43  num_of_split_atoms:                     0
% 6.54/1.43  num_of_reused_defs:                     0
% 6.54/1.43  num_eq_ax_congr_red:                    17
% 6.54/1.43  num_of_sem_filtered_clauses:            1
% 6.54/1.43  num_of_subtypes:                        5
% 6.54/1.43  monotx_restored_types:                  0
% 6.54/1.43  sat_num_of_epr_types:                   0
% 6.54/1.43  sat_num_of_non_cyclic_types:            0
% 6.54/1.43  sat_guarded_non_collapsed_types:        1
% 6.54/1.43  num_pure_diseq_elim:                    0
% 6.54/1.43  simp_replaced_by:                       0
% 6.54/1.43  res_preprocessed:                       210
% 6.54/1.43  prep_upred:                             0
% 6.54/1.43  prep_unflattend:                        12
% 6.54/1.43  smt_new_axioms:                         0
% 6.54/1.43  pred_elim_cands:                        9
% 6.54/1.43  pred_elim:                              5
% 6.54/1.43  pred_elim_cl:                           7
% 6.54/1.43  pred_elim_cycles:                       7
% 6.54/1.43  merged_defs:                            8
% 6.54/1.43  merged_defs_ncl:                        0
% 6.54/1.43  bin_hyper_res:                          8
% 6.54/1.43  prep_cycles:                            4
% 6.54/1.43  pred_elim_time:                         0.003
% 6.54/1.43  splitting_time:                         0.
% 6.54/1.43  sem_filter_time:                        0.
% 6.54/1.43  monotx_time:                            0.
% 6.54/1.43  subtype_inf_time:                       0.001
% 6.54/1.43  
% 6.54/1.43  ------ Problem properties
% 6.54/1.43  
% 6.54/1.43  clauses:                                40
% 6.54/1.43  conjectures:                            22
% 6.54/1.43  epr:                                    18
% 6.54/1.43  horn:                                   34
% 6.54/1.43  ground:                                 23
% 6.54/1.43  unary:                                  21
% 6.54/1.43  binary:                                 4
% 6.54/1.43  lits:                                   141
% 6.54/1.43  lits_eq:                                6
% 6.54/1.43  fd_pure:                                0
% 6.54/1.43  fd_pseudo:                              0
% 6.54/1.43  fd_cond:                                0
% 6.54/1.43  fd_pseudo_cond:                         1
% 6.54/1.43  ac_symbols:                             0
% 6.54/1.43  
% 6.54/1.43  ------ Propositional Solver
% 6.54/1.43  
% 6.54/1.43  prop_solver_calls:                      28
% 6.54/1.43  prop_fast_solver_calls:                 2408
% 6.54/1.43  smt_solver_calls:                       0
% 6.54/1.43  smt_fast_solver_calls:                  0
% 6.54/1.43  prop_num_of_clauses:                    6099
% 6.54/1.43  prop_preprocess_simplified:             10600
% 6.54/1.43  prop_fo_subsumed:                       215
% 6.54/1.43  prop_solver_time:                       0.
% 6.54/1.43  smt_solver_time:                        0.
% 6.54/1.43  smt_fast_solver_time:                   0.
% 6.54/1.43  prop_fast_solver_time:                  0.
% 6.54/1.43  prop_unsat_core_time:                   0.
% 6.54/1.43  
% 6.54/1.43  ------ QBF
% 6.54/1.43  
% 6.54/1.43  qbf_q_res:                              0
% 6.54/1.43  qbf_num_tautologies:                    0
% 6.54/1.43  qbf_prep_cycles:                        0
% 6.54/1.43  
% 6.54/1.43  ------ BMC1
% 6.54/1.43  
% 6.54/1.43  bmc1_current_bound:                     -1
% 6.54/1.43  bmc1_last_solved_bound:                 -1
% 6.54/1.43  bmc1_unsat_core_size:                   -1
% 6.54/1.43  bmc1_unsat_core_parents_size:           -1
% 6.54/1.43  bmc1_merge_next_fun:                    0
% 6.54/1.43  bmc1_unsat_core_clauses_time:           0.
% 6.54/1.43  
% 6.54/1.43  ------ Instantiation
% 6.54/1.43  
% 6.54/1.43  inst_num_of_clauses:                    1450
% 6.54/1.43  inst_num_in_passive:                    370
% 6.54/1.43  inst_num_in_active:                     658
% 6.54/1.43  inst_num_in_unprocessed:                422
% 6.54/1.43  inst_num_of_loops:                      720
% 6.54/1.43  inst_num_of_learning_restarts:          0
% 6.54/1.43  inst_num_moves_active_passive:          58
% 6.54/1.43  inst_lit_activity:                      0
% 6.54/1.43  inst_lit_activity_moves:                0
% 6.54/1.43  inst_num_tautologies:                   0
% 6.54/1.43  inst_num_prop_implied:                  0
% 6.54/1.43  inst_num_existing_simplified:           0
% 6.54/1.43  inst_num_eq_res_simplified:             0
% 6.54/1.43  inst_num_child_elim:                    0
% 6.54/1.43  inst_num_of_dismatching_blockings:      381
% 6.54/1.43  inst_num_of_non_proper_insts:           1018
% 6.54/1.43  inst_num_of_duplicates:                 0
% 6.54/1.43  inst_inst_num_from_inst_to_res:         0
% 6.54/1.43  inst_dismatching_checking_time:         0.
% 6.54/1.43  
% 6.54/1.43  ------ Resolution
% 6.54/1.43  
% 6.54/1.43  res_num_of_clauses:                     0
% 6.54/1.43  res_num_in_passive:                     0
% 6.54/1.43  res_num_in_active:                      0
% 6.54/1.43  res_num_of_loops:                       214
% 6.54/1.43  res_forward_subset_subsumed:            39
% 6.54/1.43  res_backward_subset_subsumed:           0
% 6.54/1.43  res_forward_subsumed:                   0
% 6.54/1.43  res_backward_subsumed:                  0
% 6.54/1.43  res_forward_subsumption_resolution:     0
% 6.54/1.43  res_backward_subsumption_resolution:    0
% 6.54/1.43  res_clause_to_clause_subsumption:       751
% 6.54/1.43  res_orphan_elimination:                 0
% 6.54/1.43  res_tautology_del:                      63
% 6.54/1.43  res_num_eq_res_simplified:              0
% 6.54/1.43  res_num_sel_changes:                    0
% 6.54/1.43  res_moves_from_active_to_pass:          0
% 6.54/1.43  
% 6.54/1.43  ------ Superposition
% 6.54/1.43  
% 6.54/1.43  sup_time_total:                         0.
% 6.54/1.43  sup_time_generating:                    0.
% 6.54/1.43  sup_time_sim_full:                      0.
% 6.54/1.43  sup_time_sim_immed:                     0.
% 6.54/1.43  
% 6.54/1.43  sup_num_of_clauses:                     247
% 6.54/1.43  sup_num_in_active:                      127
% 6.54/1.43  sup_num_in_passive:                     120
% 6.54/1.43  sup_num_of_loops:                       142
% 6.54/1.43  sup_fw_superposition:                   190
% 6.54/1.43  sup_bw_superposition:                   183
% 6.54/1.43  sup_immediate_simplified:               130
% 6.54/1.43  sup_given_eliminated:                   0
% 6.54/1.43  comparisons_done:                       0
% 6.54/1.43  comparisons_avoided:                    0
% 6.54/1.43  
% 6.54/1.43  ------ Simplifications
% 6.54/1.43  
% 6.54/1.43  
% 6.54/1.43  sim_fw_subset_subsumed:                 17
% 6.54/1.43  sim_bw_subset_subsumed:                 20
% 6.54/1.43  sim_fw_subsumed:                        31
% 6.54/1.43  sim_bw_subsumed:                        0
% 6.54/1.43  sim_fw_subsumption_res:                 16
% 6.54/1.43  sim_bw_subsumption_res:                 0
% 6.54/1.43  sim_tautology_del:                      6
% 6.54/1.43  sim_eq_tautology_del:                   20
% 6.54/1.43  sim_eq_res_simp:                        0
% 6.54/1.43  sim_fw_demodulated:                     42
% 6.54/1.43  sim_bw_demodulated:                     15
% 6.54/1.43  sim_light_normalised:                   105
% 6.54/1.43  sim_joinable_taut:                      0
% 6.54/1.43  sim_joinable_simp:                      0
% 6.54/1.43  sim_ac_normalised:                      0
% 6.54/1.43  sim_smt_subsumption:                    0
% 6.54/1.43  
%------------------------------------------------------------------------------
