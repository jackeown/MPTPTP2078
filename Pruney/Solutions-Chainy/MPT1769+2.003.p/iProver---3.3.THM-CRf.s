%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:01 EST 2020

% Result     : Theorem 15.47s
% Output     : CNFRefutation 15.47s
% Verified   : 
% Statistics : Number of formulae       :  286 (27661 expanded)
%              Number of clauses        :  193 (4195 expanded)
%              Number of leaves         :   21 (12050 expanded)
%              Depth                    :   31
%              Number of atoms          : 1796 (611189 expanded)
%              Number of equality atoms :  612 (36310 expanded)
%              Maximal formula depth    :   26 (   7 average)
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

fof(f85,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f95,plain,(
    sK0 = sK3 ),
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

fof(f83,plain,(
    m1_pre_topc(sK2,sK0) ),
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

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f61])).

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
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( m1_pre_topc(X3,X2)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) )
                           => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
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

fof(f97,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f91,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f89,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f98,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_33,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_918,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_1864,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_918])).

cnf(c_23,negated_conjecture,
    ( sK0 = sK3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_928,negated_conjecture,
    ( sK0 = sK3 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1876,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1864,c_928])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_927,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1855,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

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

cnf(c_570,plain,
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

cnf(c_571,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK4)
    | sK6 = sK4 ),
    inference(unflattening,[status(thm)],[c_570])).

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

cnf(c_573,plain,
    ( sK6 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_39,c_37,c_32,c_31,c_30,c_26,c_25,c_24,c_97,c_101])).

cnf(c_907,plain,
    ( sK6 = sK4 ),
    inference(subtyping,[status(esa)],[c_573])).

cnf(c_1879,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1855,c_907,c_928])).

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

cnf(c_939,plain,
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

cnf(c_1844,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_939])).

cnf(c_3146,plain,
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
    inference(superposition,[status(thm)],[c_1879,c_1844])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_944,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(X0_58,X1_58,X0_55,X2_58) = k7_relat_1(X0_55,X2_58) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1839,plain,
    ( k2_partfun1(X0_58,X1_58,X0_55,X2_58) = k7_relat_1(X0_55,X2_58)
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_944])).

cnf(c_2354,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_58) = k7_relat_1(sK4,X0_58)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1879,c_1839])).

cnf(c_53,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2772,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_58) = k7_relat_1(sK4,X0_58) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2354,c_53])).

cnf(c_3148,plain,
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
    inference(demodulation,[status(thm)],[c_3146,c_2772])).

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

cnf(c_5198,plain,
    ( m1_pre_topc(X0_59,sK0) != iProver_top
    | k2_tmap_1(sK0,sK1,sK4,X0_59) = k7_relat_1(sK4,u1_struct_0(X0_59)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3148,c_43,c_44,c_45,c_46,c_47,c_48,c_53,c_54])).

cnf(c_5199,plain,
    ( k2_tmap_1(sK0,sK1,sK4,X0_59) = k7_relat_1(sK4,u1_struct_0(X0_59))
    | m1_pre_topc(X0_59,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5198])).

cnf(c_5205,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK0) = k7_relat_1(sK4,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_1876,c_5199])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_0,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_548,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_2,c_0])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_552,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_548,c_2,c_1,c_0])).

cnf(c_908,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
    | k7_relat_1(X0_55,X0_58) = X0_55 ),
    inference(subtyping,[status(esa)],[c_552])).

cnf(c_1874,plain,
    ( k7_relat_1(X0_55,X0_58) = X0_55
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_908])).

cnf(c_4475,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK0)) = sK4 ),
    inference(superposition,[status(thm)],[c_1879,c_1874])).

cnf(c_5206,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK0) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_5205,c_4475])).

cnf(c_35,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_916,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_1866,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_916])).

cnf(c_5204,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1866,c_5199])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_938,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
    | m1_subset_1(k2_tmap_1(X0_59,X1_59,X0_55,X2_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59))))
    | ~ l1_struct_0(X1_59)
    | ~ l1_struct_0(X2_59)
    | ~ l1_struct_0(X0_59)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1845,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_59,X1_59,X0_55,X2_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59)))) = iProver_top
    | l1_struct_0(X1_59) != iProver_top
    | l1_struct_0(X2_59) != iProver_top
    | l1_struct_0(X0_59) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_938])).

cnf(c_4,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_943,plain,
    ( r2_funct_2(X0_58,X1_58,X0_55,X0_55)
    | ~ v1_funct_2(X0_55,X0_58,X1_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1840,plain,
    ( r2_funct_2(X0_58,X1_58,X0_55,X0_55) = iProver_top
    | v1_funct_2(X0_55,X0_58,X1_58) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_943])).

cnf(c_3059,plain,
    ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(X1_59),k2_tmap_1(X2_59,X1_59,X0_55,X0_59),k2_tmap_1(X2_59,X1_59,X0_55,X0_59)) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X2_59),u1_struct_0(X1_59)) != iProver_top
    | v1_funct_2(k2_tmap_1(X2_59,X1_59,X0_55,X0_59),u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59)))) != iProver_top
    | l1_struct_0(X1_59) != iProver_top
    | l1_struct_0(X0_59) != iProver_top
    | l1_struct_0(X2_59) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(X2_59,X1_59,X0_55,X0_59)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1845,c_1840])).

cnf(c_18,plain,
    ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_tmap_1(X3,X1,X4,X0))
    | r2_funct_2(u1_struct_0(X5),u1_struct_0(X1),k3_tmap_1(X3,X1,X0,X5,X2),k2_tmap_1(X3,X1,X4,X5))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_pre_topc(X5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X5,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_932,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_59),u1_struct_0(X1_59),X0_55,k2_tmap_1(X2_59,X1_59,X1_55,X0_59))
    | r2_funct_2(u1_struct_0(X3_59),u1_struct_0(X1_59),k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55),k2_tmap_1(X2_59,X1_59,X1_55,X3_59))
    | ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
    | ~ v1_funct_2(X1_55,u1_struct_0(X2_59),u1_struct_0(X1_59))
    | ~ m1_pre_topc(X3_59,X2_59)
    | ~ m1_pre_topc(X0_59,X2_59)
    | ~ m1_pre_topc(X3_59,X0_59)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59))))
    | ~ v2_pre_topc(X1_59)
    | ~ v2_pre_topc(X2_59)
    | v2_struct_0(X3_59)
    | v2_struct_0(X1_59)
    | v2_struct_0(X0_59)
    | v2_struct_0(X2_59)
    | ~ l1_pre_topc(X1_59)
    | ~ l1_pre_topc(X2_59)
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X1_55) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1851,plain,
    ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(X1_59),X0_55,k2_tmap_1(X2_59,X1_59,X1_55,X0_59)) != iProver_top
    | r2_funct_2(u1_struct_0(X3_59),u1_struct_0(X1_59),k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55),k2_tmap_1(X2_59,X1_59,X1_55,X3_59)) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
    | v1_funct_2(X1_55,u1_struct_0(X2_59),u1_struct_0(X1_59)) != iProver_top
    | m1_pre_topc(X3_59,X0_59) != iProver_top
    | m1_pre_topc(X0_59,X2_59) != iProver_top
    | m1_pre_topc(X3_59,X2_59) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59)))) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(X2_59) != iProver_top
    | v2_struct_0(X3_59) = iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(X2_59) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top
    | l1_pre_topc(X2_59) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_932])).

cnf(c_5824,plain,
    ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(X1_59),k3_tmap_1(X2_59,X1_59,X3_59,X0_59,k2_tmap_1(X2_59,X1_59,X0_55,X3_59)),k2_tmap_1(X2_59,X1_59,X0_55,X0_59)) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X2_59),u1_struct_0(X1_59)) != iProver_top
    | v1_funct_2(k2_tmap_1(X2_59,X1_59,X0_55,X3_59),u1_struct_0(X3_59),u1_struct_0(X1_59)) != iProver_top
    | m1_pre_topc(X3_59,X2_59) != iProver_top
    | m1_pre_topc(X0_59,X2_59) != iProver_top
    | m1_pre_topc(X0_59,X3_59) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X2_59,X1_59,X0_55,X3_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_59),u1_struct_0(X1_59)))) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(X2_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v2_struct_0(X2_59) = iProver_top
    | v2_struct_0(X3_59) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top
    | l1_pre_topc(X2_59) != iProver_top
    | l1_struct_0(X1_59) != iProver_top
    | l1_struct_0(X3_59) != iProver_top
    | l1_struct_0(X2_59) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(X2_59,X1_59,X0_55,X3_59)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3059,c_1851])).

cnf(c_21804,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_59,sK2,k2_tmap_1(sK0,sK1,sK4,X0_59)),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X0_59),u1_struct_0(X0_59),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_59,sK0) != iProver_top
    | m1_pre_topc(sK2,X0_59) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(X0_59) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_59)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5204,c_5824])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_49,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_50,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_55,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_100,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_102,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_911,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(subtyping,[status(esa)],[c_40])).

cnf(c_1871,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_911])).

cnf(c_941,plain,
    ( ~ l1_pre_topc(X0_59)
    | l1_struct_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1842,plain,
    ( l1_pre_topc(X0_59) != iProver_top
    | l1_struct_0(X0_59) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_941])).

cnf(c_2460,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1871,c_1842])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_936,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
    | ~ l1_struct_0(X1_59)
    | ~ l1_struct_0(X2_59)
    | ~ l1_struct_0(X0_59)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k2_tmap_1(X0_59,X1_59,X0_55,X2_59)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1847,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
    | l1_struct_0(X1_59) != iProver_top
    | l1_struct_0(X2_59) != iProver_top
    | l1_struct_0(X0_59) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_59,X1_59,X0_55,X2_59)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_936])).

cnf(c_2578,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | l1_struct_0(X0_59) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1879,c_1847])).

cnf(c_3253,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
    | l1_struct_0(X0_59) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2578,c_48,c_53,c_54,c_102,c_2460])).

cnf(c_3254,plain,
    ( l1_struct_0(X0_59) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3253])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_937,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
    | v1_funct_2(k2_tmap_1(X0_59,X1_59,X0_55,X2_59),u1_struct_0(X2_59),u1_struct_0(X1_59))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
    | ~ l1_struct_0(X1_59)
    | ~ l1_struct_0(X2_59)
    | ~ l1_struct_0(X0_59)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_17527,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X0_59),u1_struct_0(X0_59),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_59)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_937])).

cnf(c_17528,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X0_59),u1_struct_0(X0_59),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_59) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17527])).

cnf(c_18704,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_59)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_938])).

cnf(c_18705,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_59) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18704])).

cnf(c_24386,plain,
    ( v2_struct_0(X0_59) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_59,sK2,k2_tmap_1(sK0,sK1,sK4,X0_59)),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
    | m1_pre_topc(X0_59,sK0) != iProver_top
    | m1_pre_topc(sK2,X0_59) != iProver_top
    | l1_struct_0(X0_59) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21804,c_43,c_44,c_45,c_46,c_47,c_48,c_49,c_50,c_53,c_54,c_55,c_102,c_2460,c_3254,c_17528,c_18705])).

cnf(c_24387,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_59,sK2,k2_tmap_1(sK0,sK1,sK4,X0_59)),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
    | m1_pre_topc(X0_59,sK0) != iProver_top
    | m1_pre_topc(sK2,X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_struct_0(X0_59) != iProver_top ),
    inference(renaming,[status(thm)],[c_24386])).

cnf(c_21,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_929,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1854,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_929])).

cnf(c_1880,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1854,c_907,c_928])).

cnf(c_5295,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5204,c_1880])).

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

cnf(c_935,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
    | ~ m1_pre_topc(X0_59,X2_59)
    | ~ m1_pre_topc(X3_59,X2_59)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
    | m1_subset_1(k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_59),u1_struct_0(X1_59))))
    | ~ v2_pre_topc(X1_59)
    | ~ v2_pre_topc(X2_59)
    | v2_struct_0(X2_59)
    | v2_struct_0(X1_59)
    | ~ l1_pre_topc(X1_59)
    | ~ l1_pre_topc(X2_59)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1848,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
    | m1_pre_topc(X0_59,X2_59) != iProver_top
    | m1_pre_topc(X3_59,X2_59) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_59),u1_struct_0(X1_59)))) = iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(X2_59) != iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v2_struct_0(X2_59) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top
    | l1_pre_topc(X2_59) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_935])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_924,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1858,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_924])).

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

cnf(c_942,plain,
    ( ~ r2_funct_2(X0_58,X1_58,X0_55,X1_55)
    | ~ v1_funct_2(X1_55,X0_58,X1_58)
    | ~ v1_funct_2(X0_55,X0_58,X1_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X1_55)
    | X1_55 = X0_55 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1841,plain,
    ( X0_55 = X1_55
    | r2_funct_2(X0_58,X1_58,X1_55,X0_55) != iProver_top
    | v1_funct_2(X1_55,X0_58,X1_58) != iProver_top
    | v1_funct_2(X0_55,X0_58,X1_58) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_942])).

cnf(c_2927,plain,
    ( sK5 = X0_55
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1858,c_1841])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_56,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_57,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3311,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | sK5 = X0_55
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2927,c_56,c_57])).

cnf(c_3312,plain,
    ( sK5 = X0_55
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_3311])).

cnf(c_3664,plain,
    ( k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55) = sK5
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55),sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X1_59),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | m1_pre_topc(sK2,X0_59) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_59),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1848,c_3312])).

cnf(c_7093,plain,
    ( l1_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_59),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_59) != iProver_top
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X1_59),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55),sK5) != iProver_top
    | k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55) = sK5
    | v2_struct_0(X0_59) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3664,c_46,c_47,c_48])).

cnf(c_7094,plain,
    ( k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55) = sK5
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55),sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X1_59),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | m1_pre_topc(sK2,X0_59) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_59),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7093])).

cnf(c_7097,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = sK5
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5295,c_7094])).

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

cnf(c_934,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
    | v1_funct_2(k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55),u1_struct_0(X3_59),u1_struct_0(X1_59))
    | ~ m1_pre_topc(X3_59,X2_59)
    | ~ m1_pre_topc(X0_59,X2_59)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
    | ~ v2_pre_topc(X1_59)
    | ~ v2_pre_topc(X2_59)
    | v2_struct_0(X1_59)
    | v2_struct_0(X2_59)
    | ~ l1_pre_topc(X1_59)
    | ~ l1_pre_topc(X2_59)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2242,plain,
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
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_2509,plain,
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
    inference(instantiation,[status(thm)],[c_2242])).

cnf(c_3201,plain,
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
    inference(instantiation,[status(thm)],[c_2509])).

cnf(c_3202,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_3201])).

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

cnf(c_933,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
    | ~ m1_pre_topc(X0_59,X2_59)
    | ~ m1_pre_topc(X3_59,X2_59)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
    | ~ v2_pre_topc(X1_59)
    | ~ v2_pre_topc(X2_59)
    | v2_struct_0(X2_59)
    | v2_struct_0(X1_59)
    | ~ l1_pre_topc(X1_59)
    | ~ l1_pre_topc(X2_59)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1954,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
    | ~ m1_pre_topc(X0_59,sK0)
    | ~ m1_pre_topc(X2_59,sK0)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
    | ~ v2_pre_topc(X1_59)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X1_59)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X1_59)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(sK0,X1_59,X0_59,X2_59,X0_55)) ),
    inference(instantiation,[status(thm)],[c_933])).

cnf(c_2516,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(X0_59))
    | ~ m1_pre_topc(X1_59,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_59))))
    | ~ v2_pre_topc(X0_59)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0_59)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X0_59)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(sK0,X0_59,sK0,X1_59,X0_55)) ),
    inference(instantiation,[status(thm)],[c_1954])).

cnf(c_3234,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(X0_59))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_59))))
    | ~ v2_pre_topc(X0_59)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0_59)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X0_59)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(sK0,X0_59,sK0,sK2,X0_55)) ),
    inference(instantiation,[status(thm)],[c_2516])).

cnf(c_3841,plain,
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
    inference(instantiation,[status(thm)],[c_3234])).

cnf(c_3842,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_3841])).

cnf(c_7100,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = sK5
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7097,c_43,c_44,c_45,c_46,c_47,c_48,c_50,c_53,c_54,c_55,c_1876,c_3202,c_3842])).

cnf(c_5302,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5204,c_1845])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_940,plain,
    ( ~ m1_pre_topc(X0_59,X1_59)
    | ~ l1_pre_topc(X1_59)
    | l1_pre_topc(X0_59) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1843,plain,
    ( m1_pre_topc(X0_59,X1_59) != iProver_top
    | l1_pre_topc(X1_59) != iProver_top
    | l1_pre_topc(X0_59) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_940])).

cnf(c_2464,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1866,c_1843])).

cnf(c_2765,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2464,c_45])).

cnf(c_2769,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2765,c_1842])).

cnf(c_5713,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5302,c_48,c_53,c_54,c_55,c_102,c_2460,c_2769])).

cnf(c_5725,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK5
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5713,c_3312])).

cnf(c_1846,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_59,X1_59,X0_55,X2_59),u1_struct_0(X2_59),u1_struct_0(X1_59)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
    | l1_struct_0(X1_59) != iProver_top
    | l1_struct_0(X2_59) != iProver_top
    | l1_struct_0(X0_59) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_937])).

cnf(c_5303,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5204,c_1846])).

cnf(c_5304,plain,
    ( l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5204,c_3254])).

cnf(c_5815,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK5
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5725,c_48,c_53,c_54,c_55,c_102,c_2460,c_2769,c_5303,c_5304])).

cnf(c_7104,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = sK5
    | k7_relat_1(sK4,u1_struct_0(sK2)) = sK5 ),
    inference(superposition,[status(thm)],[c_7100,c_5815])).

cnf(c_3659,plain,
    ( k2_partfun1(u1_struct_0(X0_59),u1_struct_0(X1_59),k3_tmap_1(X2_59,X1_59,X3_59,X0_59,X0_55),X0_58) = k7_relat_1(k3_tmap_1(X2_59,X1_59,X3_59,X0_59,X0_55),X0_58)
    | v1_funct_2(X0_55,u1_struct_0(X3_59),u1_struct_0(X1_59)) != iProver_top
    | m1_pre_topc(X3_59,X2_59) != iProver_top
    | m1_pre_topc(X0_59,X2_59) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_59),u1_struct_0(X1_59)))) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(X2_59) != iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v2_struct_0(X2_59) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top
    | l1_pre_topc(X2_59) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_59,X1_59,X3_59,X0_59,X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1848,c_1839])).

cnf(c_10812,plain,
    ( k2_partfun1(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4),X0_58) = k7_relat_1(k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4),X0_58)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_59,X1_59) != iProver_top
    | m1_pre_topc(sK0,X1_59) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1879,c_3659])).

cnf(c_1850,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
    | m1_pre_topc(X0_59,X2_59) != iProver_top
    | m1_pre_topc(X3_59,X2_59) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(X2_59) != iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v2_struct_0(X2_59) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top
    | l1_pre_topc(X2_59) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_933])).

cnf(c_3161,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_59,X1_59) != iProver_top
    | m1_pre_topc(sK0,X1_59) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1879,c_1850])).

cnf(c_3439,plain,
    ( v1_funct_1(k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4)) = iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | m1_pre_topc(X0_59,X1_59) != iProver_top
    | m1_pre_topc(sK0,X1_59) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | l1_pre_topc(X1_59) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3161,c_46,c_47,c_48,c_53,c_54])).

cnf(c_3440,plain,
    ( m1_pre_topc(X0_59,X1_59) != iProver_top
    | m1_pre_topc(sK0,X1_59) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3439])).

cnf(c_11337,plain,
    ( l1_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | m1_pre_topc(sK0,X1_59) != iProver_top
    | m1_pre_topc(X0_59,X1_59) != iProver_top
    | k2_partfun1(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4),X0_58) = k7_relat_1(k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4),X0_58)
    | v2_struct_0(X1_59) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10812,c_46,c_47,c_48,c_53,c_54,c_3440])).

cnf(c_11338,plain,
    ( k2_partfun1(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4),X0_58) = k7_relat_1(k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4),X0_58)
    | m1_pre_topc(X0_59,X1_59) != iProver_top
    | m1_pre_topc(sK0,X1_59) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top ),
    inference(renaming,[status(thm)],[c_11337])).

cnf(c_11343,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),X0_58) = k7_relat_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),X0_58)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1866,c_11338])).

cnf(c_11396,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),X0_58) = k7_relat_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),X0_58) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11343,c_43,c_44,c_45,c_1876])).

cnf(c_23672,plain,
    ( k7_relat_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),X0_58) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,X0_58)
    | k7_relat_1(sK4,u1_struct_0(sK2)) = sK5 ),
    inference(superposition,[status(thm)],[c_7104,c_11396])).

cnf(c_2272,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,X0_58) = k7_relat_1(sK5,X0_58)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1858,c_1839])).

cnf(c_2448,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,X0_58) = k7_relat_1(sK5,X0_58) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2272,c_56])).

cnf(c_23687,plain,
    ( k7_relat_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),X0_58) = k7_relat_1(sK5,X0_58)
    | k7_relat_1(sK4,u1_struct_0(sK2)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_23672,c_2448])).

cnf(c_58,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2453,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1879,c_1840])).

cnf(c_5718,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5713,c_1841])).

cnf(c_6548,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5718,c_48,c_53,c_54,c_55,c_102,c_2460,c_2769,c_5303,c_5304])).

cnf(c_6549,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_6548])).

cnf(c_6551,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK5
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6549])).

cnf(c_5508,plain,
    ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_59,X0_55),k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_55,sK4) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_59,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5206,c_1851])).

cnf(c_20495,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | m1_pre_topc(X0_59,sK0) != iProver_top
    | r2_funct_2(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_59,X0_55),k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_55,sK4) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5508,c_43,c_44,c_45,c_46,c_47,c_48,c_53,c_54,c_55,c_1876])).

cnf(c_20496,plain,
    ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_59,X0_55),k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_55,sK4) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_59,sK0) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_20495])).

cnf(c_20501,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_55,sK4) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,X0_55),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_5204,c_20496])).

cnf(c_20606,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_55,sK4) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,X0_55),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20501,c_49,c_50])).

cnf(c_20607,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_55,sK4) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,X0_55),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_20606])).

cnf(c_23678,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK5
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7104,c_20607])).

cnf(c_24078,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23687,c_53,c_54,c_55,c_56,c_57,c_58,c_2453,c_6551,c_23678])).

cnf(c_24392,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_59,sK2,k2_tmap_1(sK0,sK1,sK4,X0_59)),sK5) = iProver_top
    | m1_pre_topc(X0_59,sK0) != iProver_top
    | m1_pre_topc(sK2,X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_struct_0(X0_59) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24387,c_24078])).

cnf(c_24397,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_struct_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5206,c_24392])).

cnf(c_20,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_930,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1853,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_930])).

cnf(c_1881,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1853,c_907,c_928])).

cnf(c_5296,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5204,c_1881])).

cnf(c_24114,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24078,c_5296])).

cnf(c_2452,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1858,c_1840])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24397,c_24114,c_2460,c_2452,c_1876,c_57,c_56,c_50,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.47/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.47/2.48  
% 15.47/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.47/2.48  
% 15.47/2.48  ------  iProver source info
% 15.47/2.48  
% 15.47/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.47/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.47/2.48  git: non_committed_changes: false
% 15.47/2.48  git: last_make_outside_of_git: false
% 15.47/2.48  
% 15.47/2.48  ------ 
% 15.47/2.48  
% 15.47/2.48  ------ Input Options
% 15.47/2.48  
% 15.47/2.48  --out_options                           all
% 15.47/2.48  --tptp_safe_out                         true
% 15.47/2.48  --problem_path                          ""
% 15.47/2.48  --include_path                          ""
% 15.47/2.48  --clausifier                            res/vclausify_rel
% 15.47/2.48  --clausifier_options                    ""
% 15.47/2.48  --stdin                                 false
% 15.47/2.48  --stats_out                             all
% 15.47/2.48  
% 15.47/2.48  ------ General Options
% 15.47/2.48  
% 15.47/2.48  --fof                                   false
% 15.47/2.48  --time_out_real                         305.
% 15.47/2.48  --time_out_virtual                      -1.
% 15.47/2.48  --symbol_type_check                     false
% 15.47/2.48  --clausify_out                          false
% 15.47/2.48  --sig_cnt_out                           false
% 15.47/2.48  --trig_cnt_out                          false
% 15.47/2.48  --trig_cnt_out_tolerance                1.
% 15.47/2.48  --trig_cnt_out_sk_spl                   false
% 15.47/2.48  --abstr_cl_out                          false
% 15.47/2.48  
% 15.47/2.48  ------ Global Options
% 15.47/2.48  
% 15.47/2.48  --schedule                              default
% 15.47/2.48  --add_important_lit                     false
% 15.47/2.48  --prop_solver_per_cl                    1000
% 15.47/2.48  --min_unsat_core                        false
% 15.47/2.48  --soft_assumptions                      false
% 15.47/2.48  --soft_lemma_size                       3
% 15.47/2.48  --prop_impl_unit_size                   0
% 15.47/2.48  --prop_impl_unit                        []
% 15.47/2.48  --share_sel_clauses                     true
% 15.47/2.48  --reset_solvers                         false
% 15.47/2.48  --bc_imp_inh                            [conj_cone]
% 15.47/2.48  --conj_cone_tolerance                   3.
% 15.47/2.48  --extra_neg_conj                        none
% 15.47/2.48  --large_theory_mode                     true
% 15.47/2.48  --prolific_symb_bound                   200
% 15.47/2.48  --lt_threshold                          2000
% 15.47/2.48  --clause_weak_htbl                      true
% 15.47/2.48  --gc_record_bc_elim                     false
% 15.47/2.48  
% 15.47/2.48  ------ Preprocessing Options
% 15.47/2.48  
% 15.47/2.48  --preprocessing_flag                    true
% 15.47/2.48  --time_out_prep_mult                    0.1
% 15.47/2.48  --splitting_mode                        input
% 15.47/2.48  --splitting_grd                         true
% 15.47/2.48  --splitting_cvd                         false
% 15.47/2.48  --splitting_cvd_svl                     false
% 15.47/2.48  --splitting_nvd                         32
% 15.47/2.48  --sub_typing                            true
% 15.47/2.48  --prep_gs_sim                           true
% 15.47/2.48  --prep_unflatten                        true
% 15.47/2.48  --prep_res_sim                          true
% 15.47/2.48  --prep_upred                            true
% 15.47/2.48  --prep_sem_filter                       exhaustive
% 15.47/2.48  --prep_sem_filter_out                   false
% 15.47/2.48  --pred_elim                             true
% 15.47/2.48  --res_sim_input                         true
% 15.47/2.48  --eq_ax_congr_red                       true
% 15.47/2.48  --pure_diseq_elim                       true
% 15.47/2.48  --brand_transform                       false
% 15.47/2.48  --non_eq_to_eq                          false
% 15.47/2.48  --prep_def_merge                        true
% 15.47/2.48  --prep_def_merge_prop_impl              false
% 15.47/2.48  --prep_def_merge_mbd                    true
% 15.47/2.48  --prep_def_merge_tr_red                 false
% 15.47/2.48  --prep_def_merge_tr_cl                  false
% 15.47/2.48  --smt_preprocessing                     true
% 15.47/2.48  --smt_ac_axioms                         fast
% 15.47/2.48  --preprocessed_out                      false
% 15.47/2.48  --preprocessed_stats                    false
% 15.47/2.48  
% 15.47/2.48  ------ Abstraction refinement Options
% 15.47/2.48  
% 15.47/2.48  --abstr_ref                             []
% 15.47/2.48  --abstr_ref_prep                        false
% 15.47/2.48  --abstr_ref_until_sat                   false
% 15.47/2.48  --abstr_ref_sig_restrict                funpre
% 15.47/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.47/2.48  --abstr_ref_under                       []
% 15.47/2.48  
% 15.47/2.48  ------ SAT Options
% 15.47/2.48  
% 15.47/2.48  --sat_mode                              false
% 15.47/2.48  --sat_fm_restart_options                ""
% 15.47/2.48  --sat_gr_def                            false
% 15.47/2.48  --sat_epr_types                         true
% 15.47/2.48  --sat_non_cyclic_types                  false
% 15.47/2.48  --sat_finite_models                     false
% 15.47/2.48  --sat_fm_lemmas                         false
% 15.47/2.48  --sat_fm_prep                           false
% 15.47/2.48  --sat_fm_uc_incr                        true
% 15.47/2.48  --sat_out_model                         small
% 15.47/2.48  --sat_out_clauses                       false
% 15.47/2.48  
% 15.47/2.48  ------ QBF Options
% 15.47/2.48  
% 15.47/2.48  --qbf_mode                              false
% 15.47/2.48  --qbf_elim_univ                         false
% 15.47/2.48  --qbf_dom_inst                          none
% 15.47/2.48  --qbf_dom_pre_inst                      false
% 15.47/2.48  --qbf_sk_in                             false
% 15.47/2.48  --qbf_pred_elim                         true
% 15.47/2.48  --qbf_split                             512
% 15.47/2.48  
% 15.47/2.48  ------ BMC1 Options
% 15.47/2.48  
% 15.47/2.48  --bmc1_incremental                      false
% 15.47/2.48  --bmc1_axioms                           reachable_all
% 15.47/2.48  --bmc1_min_bound                        0
% 15.47/2.48  --bmc1_max_bound                        -1
% 15.47/2.48  --bmc1_max_bound_default                -1
% 15.47/2.48  --bmc1_symbol_reachability              true
% 15.47/2.48  --bmc1_property_lemmas                  false
% 15.47/2.48  --bmc1_k_induction                      false
% 15.47/2.48  --bmc1_non_equiv_states                 false
% 15.47/2.48  --bmc1_deadlock                         false
% 15.47/2.48  --bmc1_ucm                              false
% 15.47/2.48  --bmc1_add_unsat_core                   none
% 15.47/2.48  --bmc1_unsat_core_children              false
% 15.47/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.47/2.48  --bmc1_out_stat                         full
% 15.47/2.48  --bmc1_ground_init                      false
% 15.47/2.48  --bmc1_pre_inst_next_state              false
% 15.47/2.48  --bmc1_pre_inst_state                   false
% 15.47/2.48  --bmc1_pre_inst_reach_state             false
% 15.47/2.48  --bmc1_out_unsat_core                   false
% 15.47/2.48  --bmc1_aig_witness_out                  false
% 15.47/2.48  --bmc1_verbose                          false
% 15.47/2.48  --bmc1_dump_clauses_tptp                false
% 15.47/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.47/2.48  --bmc1_dump_file                        -
% 15.47/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.47/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.47/2.48  --bmc1_ucm_extend_mode                  1
% 15.47/2.48  --bmc1_ucm_init_mode                    2
% 15.47/2.48  --bmc1_ucm_cone_mode                    none
% 15.47/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.47/2.48  --bmc1_ucm_relax_model                  4
% 15.47/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.47/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.47/2.48  --bmc1_ucm_layered_model                none
% 15.47/2.48  --bmc1_ucm_max_lemma_size               10
% 15.47/2.48  
% 15.47/2.48  ------ AIG Options
% 15.47/2.48  
% 15.47/2.48  --aig_mode                              false
% 15.47/2.48  
% 15.47/2.48  ------ Instantiation Options
% 15.47/2.48  
% 15.47/2.48  --instantiation_flag                    true
% 15.47/2.48  --inst_sos_flag                         true
% 15.47/2.48  --inst_sos_phase                        true
% 15.47/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.47/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.47/2.48  --inst_lit_sel_side                     num_symb
% 15.47/2.48  --inst_solver_per_active                1400
% 15.47/2.48  --inst_solver_calls_frac                1.
% 15.47/2.48  --inst_passive_queue_type               priority_queues
% 15.47/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.47/2.48  --inst_passive_queues_freq              [25;2]
% 15.47/2.48  --inst_dismatching                      true
% 15.47/2.48  --inst_eager_unprocessed_to_passive     true
% 15.47/2.48  --inst_prop_sim_given                   true
% 15.47/2.48  --inst_prop_sim_new                     false
% 15.47/2.48  --inst_subs_new                         false
% 15.47/2.48  --inst_eq_res_simp                      false
% 15.47/2.48  --inst_subs_given                       false
% 15.47/2.48  --inst_orphan_elimination               true
% 15.47/2.48  --inst_learning_loop_flag               true
% 15.47/2.48  --inst_learning_start                   3000
% 15.47/2.48  --inst_learning_factor                  2
% 15.47/2.48  --inst_start_prop_sim_after_learn       3
% 15.47/2.48  --inst_sel_renew                        solver
% 15.47/2.48  --inst_lit_activity_flag                true
% 15.47/2.48  --inst_restr_to_given                   false
% 15.47/2.48  --inst_activity_threshold               500
% 15.47/2.48  --inst_out_proof                        true
% 15.47/2.48  
% 15.47/2.48  ------ Resolution Options
% 15.47/2.48  
% 15.47/2.48  --resolution_flag                       true
% 15.47/2.48  --res_lit_sel                           adaptive
% 15.47/2.48  --res_lit_sel_side                      none
% 15.47/2.48  --res_ordering                          kbo
% 15.47/2.48  --res_to_prop_solver                    active
% 15.47/2.48  --res_prop_simpl_new                    false
% 15.47/2.48  --res_prop_simpl_given                  true
% 15.47/2.48  --res_passive_queue_type                priority_queues
% 15.47/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.47/2.48  --res_passive_queues_freq               [15;5]
% 15.47/2.48  --res_forward_subs                      full
% 15.47/2.48  --res_backward_subs                     full
% 15.47/2.48  --res_forward_subs_resolution           true
% 15.47/2.48  --res_backward_subs_resolution          true
% 15.47/2.48  --res_orphan_elimination                true
% 15.47/2.48  --res_time_limit                        2.
% 15.47/2.48  --res_out_proof                         true
% 15.47/2.48  
% 15.47/2.48  ------ Superposition Options
% 15.47/2.48  
% 15.47/2.48  --superposition_flag                    true
% 15.47/2.48  --sup_passive_queue_type                priority_queues
% 15.47/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.47/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.47/2.48  --demod_completeness_check              fast
% 15.47/2.48  --demod_use_ground                      true
% 15.47/2.48  --sup_to_prop_solver                    passive
% 15.47/2.48  --sup_prop_simpl_new                    true
% 15.47/2.48  --sup_prop_simpl_given                  true
% 15.47/2.48  --sup_fun_splitting                     true
% 15.47/2.48  --sup_smt_interval                      50000
% 15.47/2.48  
% 15.47/2.48  ------ Superposition Simplification Setup
% 15.47/2.48  
% 15.47/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.47/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.47/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.47/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.47/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.47/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.47/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.47/2.48  --sup_immed_triv                        [TrivRules]
% 15.47/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.48  --sup_immed_bw_main                     []
% 15.47/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.47/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.47/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.48  --sup_input_bw                          []
% 15.47/2.48  
% 15.47/2.48  ------ Combination Options
% 15.47/2.48  
% 15.47/2.48  --comb_res_mult                         3
% 15.47/2.48  --comb_sup_mult                         2
% 15.47/2.48  --comb_inst_mult                        10
% 15.47/2.48  
% 15.47/2.48  ------ Debug Options
% 15.47/2.48  
% 15.47/2.48  --dbg_backtrace                         false
% 15.47/2.48  --dbg_dump_prop_clauses                 false
% 15.47/2.48  --dbg_dump_prop_clauses_file            -
% 15.47/2.48  --dbg_out_stat                          false
% 15.47/2.48  ------ Parsing...
% 15.47/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.47/2.48  
% 15.47/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 15.47/2.48  
% 15.47/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.47/2.48  
% 15.47/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.47/2.48  ------ Proving...
% 15.47/2.48  ------ Problem Properties 
% 15.47/2.48  
% 15.47/2.48  
% 15.47/2.48  clauses                                 38
% 15.47/2.48  conjectures                             22
% 15.47/2.48  EPR                                     18
% 15.47/2.48  Horn                                    32
% 15.47/2.48  unary                                   21
% 15.47/2.48  binary                                  4
% 15.47/2.48  lits                                    139
% 15.47/2.48  lits eq                                 6
% 15.47/2.48  fd_pure                                 0
% 15.47/2.48  fd_pseudo                               0
% 15.47/2.48  fd_cond                                 0
% 15.47/2.48  fd_pseudo_cond                          1
% 15.47/2.48  AC symbols                              0
% 15.47/2.48  
% 15.47/2.48  ------ Schedule dynamic 5 is on 
% 15.47/2.48  
% 15.47/2.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.47/2.48  
% 15.47/2.48  
% 15.47/2.48  ------ 
% 15.47/2.48  Current options:
% 15.47/2.48  ------ 
% 15.47/2.48  
% 15.47/2.48  ------ Input Options
% 15.47/2.48  
% 15.47/2.48  --out_options                           all
% 15.47/2.48  --tptp_safe_out                         true
% 15.47/2.48  --problem_path                          ""
% 15.47/2.48  --include_path                          ""
% 15.47/2.48  --clausifier                            res/vclausify_rel
% 15.47/2.48  --clausifier_options                    ""
% 15.47/2.48  --stdin                                 false
% 15.47/2.48  --stats_out                             all
% 15.47/2.48  
% 15.47/2.48  ------ General Options
% 15.47/2.48  
% 15.47/2.48  --fof                                   false
% 15.47/2.48  --time_out_real                         305.
% 15.47/2.48  --time_out_virtual                      -1.
% 15.47/2.48  --symbol_type_check                     false
% 15.47/2.48  --clausify_out                          false
% 15.47/2.48  --sig_cnt_out                           false
% 15.47/2.48  --trig_cnt_out                          false
% 15.47/2.48  --trig_cnt_out_tolerance                1.
% 15.47/2.48  --trig_cnt_out_sk_spl                   false
% 15.47/2.48  --abstr_cl_out                          false
% 15.47/2.48  
% 15.47/2.48  ------ Global Options
% 15.47/2.48  
% 15.47/2.48  --schedule                              default
% 15.47/2.48  --add_important_lit                     false
% 15.47/2.48  --prop_solver_per_cl                    1000
% 15.47/2.48  --min_unsat_core                        false
% 15.47/2.48  --soft_assumptions                      false
% 15.47/2.48  --soft_lemma_size                       3
% 15.47/2.48  --prop_impl_unit_size                   0
% 15.47/2.48  --prop_impl_unit                        []
% 15.47/2.48  --share_sel_clauses                     true
% 15.47/2.48  --reset_solvers                         false
% 15.47/2.48  --bc_imp_inh                            [conj_cone]
% 15.47/2.48  --conj_cone_tolerance                   3.
% 15.47/2.48  --extra_neg_conj                        none
% 15.47/2.48  --large_theory_mode                     true
% 15.47/2.48  --prolific_symb_bound                   200
% 15.47/2.48  --lt_threshold                          2000
% 15.47/2.48  --clause_weak_htbl                      true
% 15.47/2.48  --gc_record_bc_elim                     false
% 15.47/2.48  
% 15.47/2.48  ------ Preprocessing Options
% 15.47/2.48  
% 15.47/2.48  --preprocessing_flag                    true
% 15.47/2.48  --time_out_prep_mult                    0.1
% 15.47/2.48  --splitting_mode                        input
% 15.47/2.48  --splitting_grd                         true
% 15.47/2.48  --splitting_cvd                         false
% 15.47/2.48  --splitting_cvd_svl                     false
% 15.47/2.48  --splitting_nvd                         32
% 15.47/2.48  --sub_typing                            true
% 15.47/2.48  --prep_gs_sim                           true
% 15.47/2.48  --prep_unflatten                        true
% 15.47/2.48  --prep_res_sim                          true
% 15.47/2.48  --prep_upred                            true
% 15.47/2.48  --prep_sem_filter                       exhaustive
% 15.47/2.48  --prep_sem_filter_out                   false
% 15.47/2.48  --pred_elim                             true
% 15.47/2.48  --res_sim_input                         true
% 15.47/2.48  --eq_ax_congr_red                       true
% 15.47/2.48  --pure_diseq_elim                       true
% 15.47/2.48  --brand_transform                       false
% 15.47/2.48  --non_eq_to_eq                          false
% 15.47/2.48  --prep_def_merge                        true
% 15.47/2.48  --prep_def_merge_prop_impl              false
% 15.47/2.48  --prep_def_merge_mbd                    true
% 15.47/2.48  --prep_def_merge_tr_red                 false
% 15.47/2.48  --prep_def_merge_tr_cl                  false
% 15.47/2.48  --smt_preprocessing                     true
% 15.47/2.48  --smt_ac_axioms                         fast
% 15.47/2.48  --preprocessed_out                      false
% 15.47/2.48  --preprocessed_stats                    false
% 15.47/2.48  
% 15.47/2.48  ------ Abstraction refinement Options
% 15.47/2.48  
% 15.47/2.48  --abstr_ref                             []
% 15.47/2.48  --abstr_ref_prep                        false
% 15.47/2.48  --abstr_ref_until_sat                   false
% 15.47/2.48  --abstr_ref_sig_restrict                funpre
% 15.47/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.47/2.48  --abstr_ref_under                       []
% 15.47/2.48  
% 15.47/2.48  ------ SAT Options
% 15.47/2.48  
% 15.47/2.48  --sat_mode                              false
% 15.47/2.48  --sat_fm_restart_options                ""
% 15.47/2.48  --sat_gr_def                            false
% 15.47/2.48  --sat_epr_types                         true
% 15.47/2.48  --sat_non_cyclic_types                  false
% 15.47/2.48  --sat_finite_models                     false
% 15.47/2.48  --sat_fm_lemmas                         false
% 15.47/2.48  --sat_fm_prep                           false
% 15.47/2.48  --sat_fm_uc_incr                        true
% 15.47/2.48  --sat_out_model                         small
% 15.47/2.48  --sat_out_clauses                       false
% 15.47/2.48  
% 15.47/2.48  ------ QBF Options
% 15.47/2.48  
% 15.47/2.48  --qbf_mode                              false
% 15.47/2.48  --qbf_elim_univ                         false
% 15.47/2.48  --qbf_dom_inst                          none
% 15.47/2.48  --qbf_dom_pre_inst                      false
% 15.47/2.48  --qbf_sk_in                             false
% 15.47/2.48  --qbf_pred_elim                         true
% 15.47/2.48  --qbf_split                             512
% 15.47/2.48  
% 15.47/2.48  ------ BMC1 Options
% 15.47/2.48  
% 15.47/2.48  --bmc1_incremental                      false
% 15.47/2.48  --bmc1_axioms                           reachable_all
% 15.47/2.48  --bmc1_min_bound                        0
% 15.47/2.48  --bmc1_max_bound                        -1
% 15.47/2.48  --bmc1_max_bound_default                -1
% 15.47/2.48  --bmc1_symbol_reachability              true
% 15.47/2.48  --bmc1_property_lemmas                  false
% 15.47/2.48  --bmc1_k_induction                      false
% 15.47/2.48  --bmc1_non_equiv_states                 false
% 15.47/2.48  --bmc1_deadlock                         false
% 15.47/2.48  --bmc1_ucm                              false
% 15.47/2.48  --bmc1_add_unsat_core                   none
% 15.47/2.48  --bmc1_unsat_core_children              false
% 15.47/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.47/2.48  --bmc1_out_stat                         full
% 15.47/2.48  --bmc1_ground_init                      false
% 15.47/2.48  --bmc1_pre_inst_next_state              false
% 15.47/2.48  --bmc1_pre_inst_state                   false
% 15.47/2.48  --bmc1_pre_inst_reach_state             false
% 15.47/2.48  --bmc1_out_unsat_core                   false
% 15.47/2.48  --bmc1_aig_witness_out                  false
% 15.47/2.48  --bmc1_verbose                          false
% 15.47/2.48  --bmc1_dump_clauses_tptp                false
% 15.47/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.47/2.48  --bmc1_dump_file                        -
% 15.47/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.47/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.47/2.48  --bmc1_ucm_extend_mode                  1
% 15.47/2.48  --bmc1_ucm_init_mode                    2
% 15.47/2.48  --bmc1_ucm_cone_mode                    none
% 15.47/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.47/2.48  --bmc1_ucm_relax_model                  4
% 15.47/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.47/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.47/2.48  --bmc1_ucm_layered_model                none
% 15.47/2.48  --bmc1_ucm_max_lemma_size               10
% 15.47/2.48  
% 15.47/2.48  ------ AIG Options
% 15.47/2.48  
% 15.47/2.48  --aig_mode                              false
% 15.47/2.48  
% 15.47/2.48  ------ Instantiation Options
% 15.47/2.48  
% 15.47/2.48  --instantiation_flag                    true
% 15.47/2.48  --inst_sos_flag                         true
% 15.47/2.48  --inst_sos_phase                        true
% 15.47/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.47/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.47/2.48  --inst_lit_sel_side                     none
% 15.47/2.48  --inst_solver_per_active                1400
% 15.47/2.48  --inst_solver_calls_frac                1.
% 15.47/2.48  --inst_passive_queue_type               priority_queues
% 15.47/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.47/2.48  --inst_passive_queues_freq              [25;2]
% 15.47/2.48  --inst_dismatching                      true
% 15.47/2.48  --inst_eager_unprocessed_to_passive     true
% 15.47/2.48  --inst_prop_sim_given                   true
% 15.47/2.48  --inst_prop_sim_new                     false
% 15.47/2.48  --inst_subs_new                         false
% 15.47/2.48  --inst_eq_res_simp                      false
% 15.47/2.48  --inst_subs_given                       false
% 15.47/2.48  --inst_orphan_elimination               true
% 15.47/2.48  --inst_learning_loop_flag               true
% 15.47/2.48  --inst_learning_start                   3000
% 15.47/2.48  --inst_learning_factor                  2
% 15.47/2.48  --inst_start_prop_sim_after_learn       3
% 15.47/2.48  --inst_sel_renew                        solver
% 15.47/2.48  --inst_lit_activity_flag                true
% 15.47/2.48  --inst_restr_to_given                   false
% 15.47/2.48  --inst_activity_threshold               500
% 15.47/2.48  --inst_out_proof                        true
% 15.47/2.48  
% 15.47/2.48  ------ Resolution Options
% 15.47/2.48  
% 15.47/2.48  --resolution_flag                       false
% 15.47/2.48  --res_lit_sel                           adaptive
% 15.47/2.48  --res_lit_sel_side                      none
% 15.47/2.48  --res_ordering                          kbo
% 15.47/2.48  --res_to_prop_solver                    active
% 15.47/2.48  --res_prop_simpl_new                    false
% 15.47/2.48  --res_prop_simpl_given                  true
% 15.47/2.48  --res_passive_queue_type                priority_queues
% 15.47/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.47/2.48  --res_passive_queues_freq               [15;5]
% 15.47/2.48  --res_forward_subs                      full
% 15.47/2.48  --res_backward_subs                     full
% 15.47/2.48  --res_forward_subs_resolution           true
% 15.47/2.48  --res_backward_subs_resolution          true
% 15.47/2.48  --res_orphan_elimination                true
% 15.47/2.48  --res_time_limit                        2.
% 15.47/2.48  --res_out_proof                         true
% 15.47/2.48  
% 15.47/2.48  ------ Superposition Options
% 15.47/2.48  
% 15.47/2.48  --superposition_flag                    true
% 15.47/2.48  --sup_passive_queue_type                priority_queues
% 15.47/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.47/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.47/2.48  --demod_completeness_check              fast
% 15.47/2.48  --demod_use_ground                      true
% 15.47/2.48  --sup_to_prop_solver                    passive
% 15.47/2.48  --sup_prop_simpl_new                    true
% 15.47/2.48  --sup_prop_simpl_given                  true
% 15.47/2.48  --sup_fun_splitting                     true
% 15.47/2.48  --sup_smt_interval                      50000
% 15.47/2.48  
% 15.47/2.48  ------ Superposition Simplification Setup
% 15.47/2.48  
% 15.47/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.47/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.47/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.47/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.47/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.47/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.47/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.47/2.48  --sup_immed_triv                        [TrivRules]
% 15.47/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.48  --sup_immed_bw_main                     []
% 15.47/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.47/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.47/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.48  --sup_input_bw                          []
% 15.47/2.48  
% 15.47/2.48  ------ Combination Options
% 15.47/2.48  
% 15.47/2.48  --comb_res_mult                         3
% 15.47/2.48  --comb_sup_mult                         2
% 15.47/2.48  --comb_inst_mult                        10
% 15.47/2.48  
% 15.47/2.48  ------ Debug Options
% 15.47/2.48  
% 15.47/2.48  --dbg_backtrace                         false
% 15.47/2.48  --dbg_dump_prop_clauses                 false
% 15.47/2.48  --dbg_dump_prop_clauses_file            -
% 15.47/2.48  --dbg_out_stat                          false
% 15.47/2.48  
% 15.47/2.48  
% 15.47/2.48  
% 15.47/2.48  
% 15.47/2.48  ------ Proving...
% 15.47/2.48  
% 15.47/2.48  
% 15.47/2.48  % SZS status Theorem for theBenchmark.p
% 15.47/2.48  
% 15.47/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.47/2.48  
% 15.47/2.48  fof(f15,conjecture,(
% 15.47/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 15.47/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f16,negated_conjecture,(
% 15.47/2.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 15.47/2.48    inference(negated_conjecture,[],[f15])).
% 15.47/2.48  
% 15.47/2.48  fof(f42,plain,(
% 15.47/2.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 15.47/2.48    inference(ennf_transformation,[],[f16])).
% 15.47/2.48  
% 15.47/2.48  fof(f43,plain,(
% 15.47/2.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 15.47/2.48    inference(flattening,[],[f42])).
% 15.47/2.48  
% 15.47/2.48  fof(f46,plain,(
% 15.47/2.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 15.47/2.48    inference(nnf_transformation,[],[f43])).
% 15.47/2.48  
% 15.47/2.48  fof(f47,plain,(
% 15.47/2.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 15.47/2.48    inference(flattening,[],[f46])).
% 15.47/2.48  
% 15.47/2.48  fof(f54,plain,(
% 15.47/2.48    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK6) & X0 = X3 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 15.47/2.48    introduced(choice_axiom,[])).
% 15.47/2.48  
% 15.47/2.48  fof(f53,plain,(
% 15.47/2.48    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 15.47/2.48    introduced(choice_axiom,[])).
% 15.47/2.48  
% 15.47/2.48  fof(f52,plain,(
% 15.47/2.48    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 15.47/2.48    introduced(choice_axiom,[])).
% 15.47/2.48  
% 15.47/2.48  fof(f51,plain,(
% 15.47/2.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK3),u1_struct_0(X1),X4,X6) & sK3 = X0 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 15.47/2.48    introduced(choice_axiom,[])).
% 15.47/2.48  
% 15.47/2.48  fof(f50,plain,(
% 15.47/2.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK2),X5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X6),X5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK2),X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 15.47/2.48    introduced(choice_axiom,[])).
% 15.47/2.48  
% 15.47/2.48  fof(f49,plain,(
% 15.47/2.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 15.47/2.48    introduced(choice_axiom,[])).
% 15.47/2.48  
% 15.47/2.48  fof(f48,plain,(
% 15.47/2.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 15.47/2.48    introduced(choice_axiom,[])).
% 15.47/2.48  
% 15.47/2.48  fof(f55,plain,(
% 15.47/2.48    (((((((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) & sK0 = sK3 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 15.47/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f47,f54,f53,f52,f51,f50,f49,f48])).
% 15.47/2.48  
% 15.47/2.48  fof(f85,plain,(
% 15.47/2.48    m1_pre_topc(sK3,sK0)),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f95,plain,(
% 15.47/2.48    sK0 = sK3),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f94,plain,(
% 15.47/2.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f9,axiom,(
% 15.47/2.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 15.47/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f30,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 15.47/2.48    inference(ennf_transformation,[],[f9])).
% 15.47/2.48  
% 15.47/2.48  fof(f31,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 15.47/2.48    inference(flattening,[],[f30])).
% 15.47/2.48  
% 15.47/2.48  fof(f45,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 15.47/2.48    inference(nnf_transformation,[],[f31])).
% 15.47/2.48  
% 15.47/2.48  fof(f65,plain,(
% 15.47/2.48    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f45])).
% 15.47/2.48  
% 15.47/2.48  fof(f96,plain,(
% 15.47/2.48    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f79,plain,(
% 15.47/2.48    ~v2_struct_0(sK1)),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f81,plain,(
% 15.47/2.48    l1_pre_topc(sK1)),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f86,plain,(
% 15.47/2.48    v1_funct_1(sK4)),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f87,plain,(
% 15.47/2.48    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f88,plain,(
% 15.47/2.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f92,plain,(
% 15.47/2.48    v1_funct_1(sK6)),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f93,plain,(
% 15.47/2.48    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f8,axiom,(
% 15.47/2.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 15.47/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f28,plain,(
% 15.47/2.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 15.47/2.48    inference(ennf_transformation,[],[f8])).
% 15.47/2.48  
% 15.47/2.48  fof(f29,plain,(
% 15.47/2.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 15.47/2.48    inference(flattening,[],[f28])).
% 15.47/2.48  
% 15.47/2.48  fof(f64,plain,(
% 15.47/2.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f29])).
% 15.47/2.48  
% 15.47/2.48  fof(f6,axiom,(
% 15.47/2.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 15.47/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f26,plain,(
% 15.47/2.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 15.47/2.48    inference(ennf_transformation,[],[f6])).
% 15.47/2.48  
% 15.47/2.48  fof(f62,plain,(
% 15.47/2.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f26])).
% 15.47/2.48  
% 15.47/2.48  fof(f10,axiom,(
% 15.47/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 15.47/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f32,plain,(
% 15.47/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.47/2.48    inference(ennf_transformation,[],[f10])).
% 15.47/2.48  
% 15.47/2.48  fof(f33,plain,(
% 15.47/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.47/2.48    inference(flattening,[],[f32])).
% 15.47/2.48  
% 15.47/2.48  fof(f67,plain,(
% 15.47/2.48    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f33])).
% 15.47/2.48  
% 15.47/2.48  fof(f4,axiom,(
% 15.47/2.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 15.47/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f22,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.47/2.48    inference(ennf_transformation,[],[f4])).
% 15.47/2.48  
% 15.47/2.48  fof(f23,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.47/2.48    inference(flattening,[],[f22])).
% 15.47/2.48  
% 15.47/2.48  fof(f59,plain,(
% 15.47/2.48    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f23])).
% 15.47/2.48  
% 15.47/2.48  fof(f76,plain,(
% 15.47/2.48    ~v2_struct_0(sK0)),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f77,plain,(
% 15.47/2.48    v2_pre_topc(sK0)),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f78,plain,(
% 15.47/2.48    l1_pre_topc(sK0)),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f80,plain,(
% 15.47/2.48    v2_pre_topc(sK1)),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f3,axiom,(
% 15.47/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 15.47/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f17,plain,(
% 15.47/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 15.47/2.48    inference(pure_predicate_removal,[],[f3])).
% 15.47/2.48  
% 15.47/2.48  fof(f21,plain,(
% 15.47/2.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.47/2.48    inference(ennf_transformation,[],[f17])).
% 15.47/2.48  
% 15.47/2.48  fof(f58,plain,(
% 15.47/2.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.47/2.48    inference(cnf_transformation,[],[f21])).
% 15.47/2.48  
% 15.47/2.48  fof(f1,axiom,(
% 15.47/2.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 15.47/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f18,plain,(
% 15.47/2.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 15.47/2.48    inference(ennf_transformation,[],[f1])).
% 15.47/2.48  
% 15.47/2.48  fof(f19,plain,(
% 15.47/2.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 15.47/2.48    inference(flattening,[],[f18])).
% 15.47/2.48  
% 15.47/2.48  fof(f56,plain,(
% 15.47/2.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f19])).
% 15.47/2.48  
% 15.47/2.48  fof(f2,axiom,(
% 15.47/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 15.47/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f20,plain,(
% 15.47/2.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.47/2.48    inference(ennf_transformation,[],[f2])).
% 15.47/2.48  
% 15.47/2.48  fof(f57,plain,(
% 15.47/2.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.47/2.48    inference(cnf_transformation,[],[f20])).
% 15.47/2.48  
% 15.47/2.48  fof(f83,plain,(
% 15.47/2.48    m1_pre_topc(sK2,sK0)),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f11,axiom,(
% 15.47/2.48    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 15.47/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f34,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 15.47/2.48    inference(ennf_transformation,[],[f11])).
% 15.47/2.48  
% 15.47/2.48  fof(f35,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 15.47/2.48    inference(flattening,[],[f34])).
% 15.47/2.48  
% 15.47/2.48  fof(f70,plain,(
% 15.47/2.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f35])).
% 15.47/2.48  
% 15.47/2.48  fof(f5,axiom,(
% 15.47/2.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 15.47/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f24,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 15.47/2.48    inference(ennf_transformation,[],[f5])).
% 15.47/2.48  
% 15.47/2.48  fof(f25,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.47/2.48    inference(flattening,[],[f24])).
% 15.47/2.48  
% 15.47/2.48  fof(f44,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.47/2.48    inference(nnf_transformation,[],[f25])).
% 15.47/2.48  
% 15.47/2.48  fof(f61,plain,(
% 15.47/2.48    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f44])).
% 15.47/2.48  
% 15.47/2.48  fof(f99,plain,(
% 15.47/2.48    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 15.47/2.48    inference(equality_resolution,[],[f61])).
% 15.47/2.48  
% 15.47/2.48  fof(f13,axiom,(
% 15.47/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_pre_topc(X3,X2) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))) => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 15.47/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f38,plain,(
% 15.47/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | (~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.47/2.48    inference(ennf_transformation,[],[f13])).
% 15.47/2.48  
% 15.47/2.48  fof(f39,plain,(
% 15.47/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.47/2.48    inference(flattening,[],[f38])).
% 15.47/2.48  
% 15.47/2.48  fof(f74,plain,(
% 15.47/2.48    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f39])).
% 15.47/2.48  
% 15.47/2.48  fof(f82,plain,(
% 15.47/2.48    ~v2_struct_0(sK2)),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f68,plain,(
% 15.47/2.48    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f35])).
% 15.47/2.48  
% 15.47/2.48  fof(f69,plain,(
% 15.47/2.48    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f35])).
% 15.47/2.48  
% 15.47/2.48  fof(f97,plain,(
% 15.47/2.48    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f12,axiom,(
% 15.47/2.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 15.47/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f36,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.47/2.48    inference(ennf_transformation,[],[f12])).
% 15.47/2.48  
% 15.47/2.48  fof(f37,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.47/2.48    inference(flattening,[],[f36])).
% 15.47/2.48  
% 15.47/2.48  fof(f73,plain,(
% 15.47/2.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f37])).
% 15.47/2.48  
% 15.47/2.48  fof(f91,plain,(
% 15.47/2.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f60,plain,(
% 15.47/2.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f44])).
% 15.47/2.48  
% 15.47/2.48  fof(f89,plain,(
% 15.47/2.48    v1_funct_1(sK5)),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f90,plain,(
% 15.47/2.48    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  fof(f72,plain,(
% 15.47/2.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f37])).
% 15.47/2.48  
% 15.47/2.48  fof(f71,plain,(
% 15.47/2.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f37])).
% 15.47/2.48  
% 15.47/2.48  fof(f7,axiom,(
% 15.47/2.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 15.47/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f27,plain,(
% 15.47/2.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.47/2.48    inference(ennf_transformation,[],[f7])).
% 15.47/2.48  
% 15.47/2.48  fof(f63,plain,(
% 15.47/2.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f27])).
% 15.47/2.48  
% 15.47/2.48  fof(f98,plain,(
% 15.47/2.48    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 15.47/2.48    inference(cnf_transformation,[],[f55])).
% 15.47/2.48  
% 15.47/2.48  cnf(c_33,negated_conjecture,
% 15.47/2.48      ( m1_pre_topc(sK3,sK0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f85]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_918,negated_conjecture,
% 15.47/2.48      ( m1_pre_topc(sK3,sK0) ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_33]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1864,plain,
% 15.47/2.48      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_918]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_23,negated_conjecture,
% 15.47/2.48      ( sK0 = sK3 ),
% 15.47/2.48      inference(cnf_transformation,[],[f95]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_928,negated_conjecture,
% 15.47/2.48      ( sK0 = sK3 ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_23]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1876,plain,
% 15.47/2.48      ( m1_pre_topc(sK0,sK0) = iProver_top ),
% 15.47/2.48      inference(light_normalisation,[status(thm)],[c_1864,c_928]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_24,negated_conjecture,
% 15.47/2.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 15.47/2.48      inference(cnf_transformation,[],[f94]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_927,negated_conjecture,
% 15.47/2.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_24]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1855,plain,
% 15.47/2.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_10,plain,
% 15.47/2.48      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 15.47/2.48      | ~ v1_funct_2(X5,X2,X3)
% 15.47/2.48      | ~ v1_funct_2(X4,X0,X1)
% 15.47/2.48      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 15.47/2.48      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.47/2.48      | v1_xboole_0(X1)
% 15.47/2.48      | v1_xboole_0(X3)
% 15.47/2.48      | ~ v1_funct_1(X5)
% 15.47/2.48      | ~ v1_funct_1(X4)
% 15.47/2.48      | X4 = X5 ),
% 15.47/2.48      inference(cnf_transformation,[],[f65]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_22,negated_conjecture,
% 15.47/2.48      ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
% 15.47/2.48      inference(cnf_transformation,[],[f96]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_570,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0,X1,X2)
% 15.47/2.48      | ~ v1_funct_2(X3,X4,X5)
% 15.47/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.47/2.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.47/2.48      | v1_xboole_0(X5)
% 15.47/2.48      | v1_xboole_0(X2)
% 15.47/2.48      | ~ v1_funct_1(X0)
% 15.47/2.48      | ~ v1_funct_1(X3)
% 15.47/2.48      | X3 = X0
% 15.47/2.48      | u1_struct_0(sK3) != X4
% 15.47/2.48      | u1_struct_0(sK0) != X1
% 15.47/2.48      | u1_struct_0(sK1) != X5
% 15.47/2.48      | u1_struct_0(sK1) != X2
% 15.47/2.48      | sK6 != X3
% 15.47/2.48      | sK4 != X0 ),
% 15.47/2.48      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_571,plain,
% 15.47/2.48      ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
% 15.47/2.48      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 15.47/2.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 15.47/2.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 15.47/2.48      | v1_xboole_0(u1_struct_0(sK1))
% 15.47/2.48      | ~ v1_funct_1(sK6)
% 15.47/2.48      | ~ v1_funct_1(sK4)
% 15.47/2.48      | sK6 = sK4 ),
% 15.47/2.48      inference(unflattening,[status(thm)],[c_570]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_39,negated_conjecture,
% 15.47/2.48      ( ~ v2_struct_0(sK1) ),
% 15.47/2.48      inference(cnf_transformation,[],[f79]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_37,negated_conjecture,
% 15.47/2.48      ( l1_pre_topc(sK1) ),
% 15.47/2.48      inference(cnf_transformation,[],[f81]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_32,negated_conjecture,
% 15.47/2.48      ( v1_funct_1(sK4) ),
% 15.47/2.48      inference(cnf_transformation,[],[f86]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_31,negated_conjecture,
% 15.47/2.48      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 15.47/2.48      inference(cnf_transformation,[],[f87]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_30,negated_conjecture,
% 15.47/2.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 15.47/2.48      inference(cnf_transformation,[],[f88]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_26,negated_conjecture,
% 15.47/2.48      ( v1_funct_1(sK6) ),
% 15.47/2.48      inference(cnf_transformation,[],[f92]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_25,negated_conjecture,
% 15.47/2.48      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 15.47/2.48      inference(cnf_transformation,[],[f93]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_8,plain,
% 15.47/2.48      ( v2_struct_0(X0)
% 15.47/2.48      | ~ v1_xboole_0(u1_struct_0(X0))
% 15.47/2.48      | ~ l1_struct_0(X0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f64]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_97,plain,
% 15.47/2.48      ( v2_struct_0(sK1)
% 15.47/2.48      | ~ v1_xboole_0(u1_struct_0(sK1))
% 15.47/2.48      | ~ l1_struct_0(sK1) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_8]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_6,plain,
% 15.47/2.48      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f62]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_101,plain,
% 15.47/2.48      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_6]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_573,plain,
% 15.47/2.48      ( sK6 = sK4 ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_571,c_39,c_37,c_32,c_31,c_30,c_26,c_25,c_24,c_97,
% 15.47/2.48                 c_101]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_907,plain,
% 15.47/2.48      ( sK6 = sK4 ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_573]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1879,plain,
% 15.47/2.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 15.47/2.48      inference(light_normalisation,[status(thm)],[c_1855,c_907,c_928]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_11,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.47/2.48      | ~ m1_pre_topc(X3,X1)
% 15.47/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.47/2.48      | ~ v2_pre_topc(X2)
% 15.47/2.48      | ~ v2_pre_topc(X1)
% 15.47/2.48      | v2_struct_0(X1)
% 15.47/2.48      | v2_struct_0(X2)
% 15.47/2.48      | ~ l1_pre_topc(X1)
% 15.47/2.48      | ~ l1_pre_topc(X2)
% 15.47/2.48      | ~ v1_funct_1(X0)
% 15.47/2.48      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 15.47/2.48      inference(cnf_transformation,[],[f67]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_939,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 15.47/2.48      | ~ m1_pre_topc(X2_59,X0_59)
% 15.47/2.48      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 15.47/2.48      | ~ v2_pre_topc(X1_59)
% 15.47/2.48      | ~ v2_pre_topc(X0_59)
% 15.47/2.48      | v2_struct_0(X1_59)
% 15.47/2.48      | v2_struct_0(X0_59)
% 15.47/2.48      | ~ l1_pre_topc(X1_59)
% 15.47/2.48      | ~ l1_pre_topc(X0_59)
% 15.47/2.48      | ~ v1_funct_1(X0_55)
% 15.47/2.48      | k2_partfun1(u1_struct_0(X0_59),u1_struct_0(X1_59),X0_55,u1_struct_0(X2_59)) = k2_tmap_1(X0_59,X1_59,X0_55,X2_59) ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_11]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1844,plain,
% 15.47/2.48      ( k2_partfun1(u1_struct_0(X0_59),u1_struct_0(X1_59),X0_55,u1_struct_0(X2_59)) = k2_tmap_1(X0_59,X1_59,X0_55,X2_59)
% 15.47/2.48      | v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
% 15.47/2.48      | m1_pre_topc(X2_59,X0_59) != iProver_top
% 15.47/2.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
% 15.47/2.48      | v2_pre_topc(X1_59) != iProver_top
% 15.47/2.48      | v2_pre_topc(X0_59) != iProver_top
% 15.47/2.48      | v2_struct_0(X1_59) = iProver_top
% 15.47/2.48      | v2_struct_0(X0_59) = iProver_top
% 15.47/2.48      | l1_pre_topc(X1_59) != iProver_top
% 15.47/2.48      | l1_pre_topc(X0_59) != iProver_top
% 15.47/2.48      | v1_funct_1(X0_55) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_939]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3146,plain,
% 15.47/2.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_59)) = k2_tmap_1(sK0,sK1,sK4,X0_59)
% 15.47/2.48      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | m1_pre_topc(X0_59,sK0) != iProver_top
% 15.47/2.48      | v2_pre_topc(sK0) != iProver_top
% 15.47/2.48      | v2_pre_topc(sK1) != iProver_top
% 15.47/2.48      | v2_struct_0(sK0) = iProver_top
% 15.47/2.48      | v2_struct_0(sK1) = iProver_top
% 15.47/2.48      | l1_pre_topc(sK0) != iProver_top
% 15.47/2.48      | l1_pre_topc(sK1) != iProver_top
% 15.47/2.48      | v1_funct_1(sK4) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1879,c_1844]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3,plain,
% 15.47/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.47/2.48      | ~ v1_funct_1(X0)
% 15.47/2.48      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 15.47/2.48      inference(cnf_transformation,[],[f59]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_944,plain,
% 15.47/2.48      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
% 15.47/2.48      | ~ v1_funct_1(X0_55)
% 15.47/2.48      | k2_partfun1(X0_58,X1_58,X0_55,X2_58) = k7_relat_1(X0_55,X2_58) ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_3]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1839,plain,
% 15.47/2.48      ( k2_partfun1(X0_58,X1_58,X0_55,X2_58) = k7_relat_1(X0_55,X2_58)
% 15.47/2.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 15.47/2.48      | v1_funct_1(X0_55) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_944]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2354,plain,
% 15.47/2.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_58) = k7_relat_1(sK4,X0_58)
% 15.47/2.48      | v1_funct_1(sK4) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1879,c_1839]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_53,plain,
% 15.47/2.48      ( v1_funct_1(sK4) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2772,plain,
% 15.47/2.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_58) = k7_relat_1(sK4,X0_58) ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_2354,c_53]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3148,plain,
% 15.47/2.48      ( k2_tmap_1(sK0,sK1,sK4,X0_59) = k7_relat_1(sK4,u1_struct_0(X0_59))
% 15.47/2.48      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | m1_pre_topc(X0_59,sK0) != iProver_top
% 15.47/2.48      | v2_pre_topc(sK0) != iProver_top
% 15.47/2.48      | v2_pre_topc(sK1) != iProver_top
% 15.47/2.48      | v2_struct_0(sK0) = iProver_top
% 15.47/2.48      | v2_struct_0(sK1) = iProver_top
% 15.47/2.48      | l1_pre_topc(sK0) != iProver_top
% 15.47/2.48      | l1_pre_topc(sK1) != iProver_top
% 15.47/2.48      | v1_funct_1(sK4) != iProver_top ),
% 15.47/2.48      inference(demodulation,[status(thm)],[c_3146,c_2772]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_42,negated_conjecture,
% 15.47/2.48      ( ~ v2_struct_0(sK0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f76]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_43,plain,
% 15.47/2.48      ( v2_struct_0(sK0) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_41,negated_conjecture,
% 15.47/2.48      ( v2_pre_topc(sK0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f77]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_44,plain,
% 15.47/2.48      ( v2_pre_topc(sK0) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_40,negated_conjecture,
% 15.47/2.48      ( l1_pre_topc(sK0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f78]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_45,plain,
% 15.47/2.48      ( l1_pre_topc(sK0) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_46,plain,
% 15.47/2.48      ( v2_struct_0(sK1) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_38,negated_conjecture,
% 15.47/2.48      ( v2_pre_topc(sK1) ),
% 15.47/2.48      inference(cnf_transformation,[],[f80]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_47,plain,
% 15.47/2.48      ( v2_pre_topc(sK1) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_48,plain,
% 15.47/2.48      ( l1_pre_topc(sK1) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_54,plain,
% 15.47/2.48      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5198,plain,
% 15.47/2.48      ( m1_pre_topc(X0_59,sK0) != iProver_top
% 15.47/2.48      | k2_tmap_1(sK0,sK1,sK4,X0_59) = k7_relat_1(sK4,u1_struct_0(X0_59)) ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_3148,c_43,c_44,c_45,c_46,c_47,c_48,c_53,c_54]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5199,plain,
% 15.47/2.48      ( k2_tmap_1(sK0,sK1,sK4,X0_59) = k7_relat_1(sK4,u1_struct_0(X0_59))
% 15.47/2.48      | m1_pre_topc(X0_59,sK0) != iProver_top ),
% 15.47/2.48      inference(renaming,[status(thm)],[c_5198]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5205,plain,
% 15.47/2.48      ( k2_tmap_1(sK0,sK1,sK4,sK0) = k7_relat_1(sK4,u1_struct_0(sK0)) ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1876,c_5199]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2,plain,
% 15.47/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.47/2.48      | v4_relat_1(X0,X1) ),
% 15.47/2.48      inference(cnf_transformation,[],[f58]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_0,plain,
% 15.47/2.48      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 15.47/2.48      inference(cnf_transformation,[],[f56]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_548,plain,
% 15.47/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.47/2.48      | ~ v1_relat_1(X0)
% 15.47/2.48      | k7_relat_1(X0,X1) = X0 ),
% 15.47/2.48      inference(resolution,[status(thm)],[c_2,c_0]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1,plain,
% 15.47/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.47/2.48      | v1_relat_1(X0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f57]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_552,plain,
% 15.47/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.47/2.48      | k7_relat_1(X0,X1) = X0 ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_548,c_2,c_1,c_0]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_908,plain,
% 15.47/2.48      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
% 15.47/2.48      | k7_relat_1(X0_55,X0_58) = X0_55 ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_552]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1874,plain,
% 15.47/2.48      ( k7_relat_1(X0_55,X0_58) = X0_55
% 15.47/2.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_908]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_4475,plain,
% 15.47/2.48      ( k7_relat_1(sK4,u1_struct_0(sK0)) = sK4 ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1879,c_1874]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5206,plain,
% 15.47/2.48      ( k2_tmap_1(sK0,sK1,sK4,sK0) = sK4 ),
% 15.47/2.48      inference(light_normalisation,[status(thm)],[c_5205,c_4475]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_35,negated_conjecture,
% 15.47/2.48      ( m1_pre_topc(sK2,sK0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f83]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_916,negated_conjecture,
% 15.47/2.48      ( m1_pre_topc(sK2,sK0) ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_35]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1866,plain,
% 15.47/2.48      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_916]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5204,plain,
% 15.47/2.48      ( k2_tmap_1(sK0,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1866,c_5199]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_12,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.47/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.47/2.48      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 15.47/2.48      | ~ l1_struct_0(X1)
% 15.47/2.48      | ~ l1_struct_0(X2)
% 15.47/2.48      | ~ l1_struct_0(X3)
% 15.47/2.48      | ~ v1_funct_1(X0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f70]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_938,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 15.47/2.48      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 15.47/2.48      | m1_subset_1(k2_tmap_1(X0_59,X1_59,X0_55,X2_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59))))
% 15.47/2.48      | ~ l1_struct_0(X1_59)
% 15.47/2.48      | ~ l1_struct_0(X2_59)
% 15.47/2.48      | ~ l1_struct_0(X0_59)
% 15.47/2.48      | ~ v1_funct_1(X0_55) ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_12]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1845,plain,
% 15.47/2.48      ( v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
% 15.47/2.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
% 15.47/2.48      | m1_subset_1(k2_tmap_1(X0_59,X1_59,X0_55,X2_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59)))) = iProver_top
% 15.47/2.48      | l1_struct_0(X1_59) != iProver_top
% 15.47/2.48      | l1_struct_0(X2_59) != iProver_top
% 15.47/2.48      | l1_struct_0(X0_59) != iProver_top
% 15.47/2.48      | v1_funct_1(X0_55) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_938]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_4,plain,
% 15.47/2.48      ( r2_funct_2(X0,X1,X2,X2)
% 15.47/2.48      | ~ v1_funct_2(X2,X0,X1)
% 15.47/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.47/2.48      | ~ v1_funct_1(X2) ),
% 15.47/2.48      inference(cnf_transformation,[],[f99]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_943,plain,
% 15.47/2.48      ( r2_funct_2(X0_58,X1_58,X0_55,X0_55)
% 15.47/2.48      | ~ v1_funct_2(X0_55,X0_58,X1_58)
% 15.47/2.48      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
% 15.47/2.48      | ~ v1_funct_1(X0_55) ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_4]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1840,plain,
% 15.47/2.48      ( r2_funct_2(X0_58,X1_58,X0_55,X0_55) = iProver_top
% 15.47/2.48      | v1_funct_2(X0_55,X0_58,X1_58) != iProver_top
% 15.47/2.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 15.47/2.48      | v1_funct_1(X0_55) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_943]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3059,plain,
% 15.47/2.48      ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(X1_59),k2_tmap_1(X2_59,X1_59,X0_55,X0_59),k2_tmap_1(X2_59,X1_59,X0_55,X0_59)) = iProver_top
% 15.47/2.48      | v1_funct_2(X0_55,u1_struct_0(X2_59),u1_struct_0(X1_59)) != iProver_top
% 15.47/2.48      | v1_funct_2(k2_tmap_1(X2_59,X1_59,X0_55,X0_59),u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
% 15.47/2.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59)))) != iProver_top
% 15.47/2.48      | l1_struct_0(X1_59) != iProver_top
% 15.47/2.48      | l1_struct_0(X0_59) != iProver_top
% 15.47/2.48      | l1_struct_0(X2_59) != iProver_top
% 15.47/2.48      | v1_funct_1(X0_55) != iProver_top
% 15.47/2.48      | v1_funct_1(k2_tmap_1(X2_59,X1_59,X0_55,X0_59)) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1845,c_1840]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_18,plain,
% 15.47/2.48      ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_tmap_1(X3,X1,X4,X0))
% 15.47/2.48      | r2_funct_2(u1_struct_0(X5),u1_struct_0(X1),k3_tmap_1(X3,X1,X0,X5,X2),k2_tmap_1(X3,X1,X4,X5))
% 15.47/2.48      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 15.47/2.48      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
% 15.47/2.48      | ~ m1_pre_topc(X5,X3)
% 15.47/2.48      | ~ m1_pre_topc(X0,X3)
% 15.47/2.48      | ~ m1_pre_topc(X5,X0)
% 15.47/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.47/2.48      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 15.47/2.48      | ~ v2_pre_topc(X1)
% 15.47/2.48      | ~ v2_pre_topc(X3)
% 15.47/2.48      | v2_struct_0(X3)
% 15.47/2.48      | v2_struct_0(X1)
% 15.47/2.48      | v2_struct_0(X0)
% 15.47/2.48      | v2_struct_0(X5)
% 15.47/2.48      | ~ l1_pre_topc(X3)
% 15.47/2.48      | ~ l1_pre_topc(X1)
% 15.47/2.48      | ~ v1_funct_1(X2)
% 15.47/2.48      | ~ v1_funct_1(X4) ),
% 15.47/2.48      inference(cnf_transformation,[],[f74]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_932,plain,
% 15.47/2.48      ( ~ r2_funct_2(u1_struct_0(X0_59),u1_struct_0(X1_59),X0_55,k2_tmap_1(X2_59,X1_59,X1_55,X0_59))
% 15.47/2.48      | r2_funct_2(u1_struct_0(X3_59),u1_struct_0(X1_59),k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55),k2_tmap_1(X2_59,X1_59,X1_55,X3_59))
% 15.47/2.48      | ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 15.47/2.48      | ~ v1_funct_2(X1_55,u1_struct_0(X2_59),u1_struct_0(X1_59))
% 15.47/2.48      | ~ m1_pre_topc(X3_59,X2_59)
% 15.47/2.48      | ~ m1_pre_topc(X0_59,X2_59)
% 15.47/2.48      | ~ m1_pre_topc(X3_59,X0_59)
% 15.47/2.48      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 15.47/2.48      | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59))))
% 15.47/2.48      | ~ v2_pre_topc(X1_59)
% 15.47/2.48      | ~ v2_pre_topc(X2_59)
% 15.47/2.48      | v2_struct_0(X3_59)
% 15.47/2.48      | v2_struct_0(X1_59)
% 15.47/2.48      | v2_struct_0(X0_59)
% 15.47/2.48      | v2_struct_0(X2_59)
% 15.47/2.48      | ~ l1_pre_topc(X1_59)
% 15.47/2.48      | ~ l1_pre_topc(X2_59)
% 15.47/2.48      | ~ v1_funct_1(X0_55)
% 15.47/2.48      | ~ v1_funct_1(X1_55) ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_18]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1851,plain,
% 15.47/2.48      ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(X1_59),X0_55,k2_tmap_1(X2_59,X1_59,X1_55,X0_59)) != iProver_top
% 15.47/2.48      | r2_funct_2(u1_struct_0(X3_59),u1_struct_0(X1_59),k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55),k2_tmap_1(X2_59,X1_59,X1_55,X3_59)) = iProver_top
% 15.47/2.48      | v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
% 15.47/2.48      | v1_funct_2(X1_55,u1_struct_0(X2_59),u1_struct_0(X1_59)) != iProver_top
% 15.47/2.48      | m1_pre_topc(X3_59,X0_59) != iProver_top
% 15.47/2.48      | m1_pre_topc(X0_59,X2_59) != iProver_top
% 15.47/2.48      | m1_pre_topc(X3_59,X2_59) != iProver_top
% 15.47/2.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
% 15.47/2.48      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59)))) != iProver_top
% 15.47/2.48      | v2_pre_topc(X1_59) != iProver_top
% 15.47/2.48      | v2_pre_topc(X2_59) != iProver_top
% 15.47/2.48      | v2_struct_0(X3_59) = iProver_top
% 15.47/2.48      | v2_struct_0(X1_59) = iProver_top
% 15.47/2.48      | v2_struct_0(X0_59) = iProver_top
% 15.47/2.48      | v2_struct_0(X2_59) = iProver_top
% 15.47/2.48      | l1_pre_topc(X1_59) != iProver_top
% 15.47/2.48      | l1_pre_topc(X2_59) != iProver_top
% 15.47/2.48      | v1_funct_1(X0_55) != iProver_top
% 15.47/2.48      | v1_funct_1(X1_55) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_932]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5824,plain,
% 15.47/2.48      ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(X1_59),k3_tmap_1(X2_59,X1_59,X3_59,X0_59,k2_tmap_1(X2_59,X1_59,X0_55,X3_59)),k2_tmap_1(X2_59,X1_59,X0_55,X0_59)) = iProver_top
% 15.47/2.48      | v1_funct_2(X0_55,u1_struct_0(X2_59),u1_struct_0(X1_59)) != iProver_top
% 15.47/2.48      | v1_funct_2(k2_tmap_1(X2_59,X1_59,X0_55,X3_59),u1_struct_0(X3_59),u1_struct_0(X1_59)) != iProver_top
% 15.47/2.48      | m1_pre_topc(X3_59,X2_59) != iProver_top
% 15.47/2.48      | m1_pre_topc(X0_59,X2_59) != iProver_top
% 15.47/2.48      | m1_pre_topc(X0_59,X3_59) != iProver_top
% 15.47/2.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59)))) != iProver_top
% 15.47/2.48      | m1_subset_1(k2_tmap_1(X2_59,X1_59,X0_55,X3_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_59),u1_struct_0(X1_59)))) != iProver_top
% 15.47/2.48      | v2_pre_topc(X1_59) != iProver_top
% 15.47/2.48      | v2_pre_topc(X2_59) != iProver_top
% 15.47/2.48      | v2_struct_0(X0_59) = iProver_top
% 15.47/2.48      | v2_struct_0(X1_59) = iProver_top
% 15.47/2.48      | v2_struct_0(X2_59) = iProver_top
% 15.47/2.48      | v2_struct_0(X3_59) = iProver_top
% 15.47/2.48      | l1_pre_topc(X1_59) != iProver_top
% 15.47/2.48      | l1_pre_topc(X2_59) != iProver_top
% 15.47/2.48      | l1_struct_0(X1_59) != iProver_top
% 15.47/2.48      | l1_struct_0(X3_59) != iProver_top
% 15.47/2.48      | l1_struct_0(X2_59) != iProver_top
% 15.47/2.48      | v1_funct_1(X0_55) != iProver_top
% 15.47/2.48      | v1_funct_1(k2_tmap_1(X2_59,X1_59,X0_55,X3_59)) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_3059,c_1851]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_21804,plain,
% 15.47/2.48      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_59,sK2,k2_tmap_1(sK0,sK1,sK4,X0_59)),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
% 15.47/2.48      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X0_59),u1_struct_0(X0_59),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | m1_pre_topc(X0_59,sK0) != iProver_top
% 15.47/2.48      | m1_pre_topc(sK2,X0_59) != iProver_top
% 15.47/2.48      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.47/2.48      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.48      | v2_pre_topc(sK0) != iProver_top
% 15.47/2.48      | v2_pre_topc(sK1) != iProver_top
% 15.47/2.48      | v2_struct_0(X0_59) = iProver_top
% 15.47/2.48      | v2_struct_0(sK0) = iProver_top
% 15.47/2.48      | v2_struct_0(sK1) = iProver_top
% 15.47/2.48      | v2_struct_0(sK2) = iProver_top
% 15.47/2.48      | l1_pre_topc(sK0) != iProver_top
% 15.47/2.48      | l1_pre_topc(sK1) != iProver_top
% 15.47/2.48      | l1_struct_0(X0_59) != iProver_top
% 15.47/2.48      | l1_struct_0(sK0) != iProver_top
% 15.47/2.48      | l1_struct_0(sK1) != iProver_top
% 15.47/2.48      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_59)) != iProver_top
% 15.47/2.48      | v1_funct_1(sK4) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_5204,c_5824]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_36,negated_conjecture,
% 15.47/2.48      ( ~ v2_struct_0(sK2) ),
% 15.47/2.48      inference(cnf_transformation,[],[f82]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_49,plain,
% 15.47/2.48      ( v2_struct_0(sK2) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_50,plain,
% 15.47/2.48      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_55,plain,
% 15.47/2.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_100,plain,
% 15.47/2.48      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_102,plain,
% 15.47/2.48      ( l1_pre_topc(sK1) != iProver_top
% 15.47/2.48      | l1_struct_0(sK1) = iProver_top ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_100]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_911,negated_conjecture,
% 15.47/2.48      ( l1_pre_topc(sK0) ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_40]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1871,plain,
% 15.47/2.48      ( l1_pre_topc(sK0) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_911]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_941,plain,
% 15.47/2.48      ( ~ l1_pre_topc(X0_59) | l1_struct_0(X0_59) ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_6]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1842,plain,
% 15.47/2.48      ( l1_pre_topc(X0_59) != iProver_top
% 15.47/2.48      | l1_struct_0(X0_59) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_941]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2460,plain,
% 15.47/2.48      ( l1_struct_0(sK0) = iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1871,c_1842]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_14,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.47/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.47/2.48      | ~ l1_struct_0(X1)
% 15.47/2.48      | ~ l1_struct_0(X2)
% 15.47/2.48      | ~ l1_struct_0(X3)
% 15.47/2.48      | ~ v1_funct_1(X0)
% 15.47/2.48      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 15.47/2.48      inference(cnf_transformation,[],[f68]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_936,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 15.47/2.48      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 15.47/2.48      | ~ l1_struct_0(X1_59)
% 15.47/2.48      | ~ l1_struct_0(X2_59)
% 15.47/2.48      | ~ l1_struct_0(X0_59)
% 15.47/2.48      | ~ v1_funct_1(X0_55)
% 15.47/2.48      | v1_funct_1(k2_tmap_1(X0_59,X1_59,X0_55,X2_59)) ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_14]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1847,plain,
% 15.47/2.48      ( v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
% 15.47/2.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
% 15.47/2.48      | l1_struct_0(X1_59) != iProver_top
% 15.47/2.48      | l1_struct_0(X2_59) != iProver_top
% 15.47/2.48      | l1_struct_0(X0_59) != iProver_top
% 15.47/2.48      | v1_funct_1(X0_55) != iProver_top
% 15.47/2.48      | v1_funct_1(k2_tmap_1(X0_59,X1_59,X0_55,X2_59)) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_936]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2578,plain,
% 15.47/2.48      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | l1_struct_0(X0_59) != iProver_top
% 15.47/2.48      | l1_struct_0(sK0) != iProver_top
% 15.47/2.48      | l1_struct_0(sK1) != iProver_top
% 15.47/2.48      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
% 15.47/2.48      | v1_funct_1(sK4) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1879,c_1847]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3253,plain,
% 15.47/2.48      ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
% 15.47/2.48      | l1_struct_0(X0_59) != iProver_top ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_2578,c_48,c_53,c_54,c_102,c_2460]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3254,plain,
% 15.47/2.48      ( l1_struct_0(X0_59) != iProver_top
% 15.47/2.48      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top ),
% 15.47/2.48      inference(renaming,[status(thm)],[c_3253]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_13,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.47/2.48      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 15.47/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.47/2.48      | ~ l1_struct_0(X1)
% 15.47/2.48      | ~ l1_struct_0(X2)
% 15.47/2.48      | ~ l1_struct_0(X3)
% 15.47/2.48      | ~ v1_funct_1(X0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f69]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_937,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 15.47/2.48      | v1_funct_2(k2_tmap_1(X0_59,X1_59,X0_55,X2_59),u1_struct_0(X2_59),u1_struct_0(X1_59))
% 15.47/2.48      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 15.47/2.48      | ~ l1_struct_0(X1_59)
% 15.47/2.48      | ~ l1_struct_0(X2_59)
% 15.47/2.48      | ~ l1_struct_0(X0_59)
% 15.47/2.48      | ~ v1_funct_1(X0_55) ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_13]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_17527,plain,
% 15.47/2.48      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X0_59),u1_struct_0(X0_59),u1_struct_0(sK1))
% 15.47/2.48      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 15.47/2.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 15.47/2.48      | ~ l1_struct_0(X0_59)
% 15.47/2.48      | ~ l1_struct_0(sK0)
% 15.47/2.48      | ~ l1_struct_0(sK1)
% 15.47/2.48      | ~ v1_funct_1(sK4) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_937]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_17528,plain,
% 15.47/2.48      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X0_59),u1_struct_0(X0_59),u1_struct_0(sK1)) = iProver_top
% 15.47/2.48      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.48      | l1_struct_0(X0_59) != iProver_top
% 15.47/2.48      | l1_struct_0(sK0) != iProver_top
% 15.47/2.48      | l1_struct_0(sK1) != iProver_top
% 15.47/2.48      | v1_funct_1(sK4) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_17527]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_18704,plain,
% 15.47/2.48      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 15.47/2.48      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK1))))
% 15.47/2.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 15.47/2.48      | ~ l1_struct_0(X0_59)
% 15.47/2.48      | ~ l1_struct_0(sK0)
% 15.47/2.48      | ~ l1_struct_0(sK1)
% 15.47/2.48      | ~ v1_funct_1(sK4) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_938]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_18705,plain,
% 15.47/2.48      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK1)))) = iProver_top
% 15.47/2.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.48      | l1_struct_0(X0_59) != iProver_top
% 15.47/2.48      | l1_struct_0(sK0) != iProver_top
% 15.47/2.48      | l1_struct_0(sK1) != iProver_top
% 15.47/2.48      | v1_funct_1(sK4) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_18704]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_24386,plain,
% 15.47/2.48      ( v2_struct_0(X0_59) = iProver_top
% 15.47/2.48      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_59,sK2,k2_tmap_1(sK0,sK1,sK4,X0_59)),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
% 15.47/2.48      | m1_pre_topc(X0_59,sK0) != iProver_top
% 15.47/2.48      | m1_pre_topc(sK2,X0_59) != iProver_top
% 15.47/2.48      | l1_struct_0(X0_59) != iProver_top ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_21804,c_43,c_44,c_45,c_46,c_47,c_48,c_49,c_50,c_53,
% 15.47/2.48                 c_54,c_55,c_102,c_2460,c_3254,c_17528,c_18705]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_24387,plain,
% 15.47/2.48      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_59,sK2,k2_tmap_1(sK0,sK1,sK4,X0_59)),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
% 15.47/2.48      | m1_pre_topc(X0_59,sK0) != iProver_top
% 15.47/2.48      | m1_pre_topc(sK2,X0_59) != iProver_top
% 15.47/2.48      | v2_struct_0(X0_59) = iProver_top
% 15.47/2.48      | l1_struct_0(X0_59) != iProver_top ),
% 15.47/2.48      inference(renaming,[status(thm)],[c_24386]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_21,negated_conjecture,
% 15.47/2.48      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 15.47/2.48      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 15.47/2.48      inference(cnf_transformation,[],[f97]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_929,negated_conjecture,
% 15.47/2.48      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 15.47/2.48      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_21]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1854,plain,
% 15.47/2.48      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) = iProver_top
% 15.47/2.48      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_929]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1880,plain,
% 15.47/2.48      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
% 15.47/2.48      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
% 15.47/2.48      inference(light_normalisation,[status(thm)],[c_1854,c_907,c_928]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5295,plain,
% 15.47/2.48      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
% 15.47/2.48      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top ),
% 15.47/2.48      inference(demodulation,[status(thm)],[c_5204,c_1880]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_15,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.47/2.48      | ~ m1_pre_topc(X3,X4)
% 15.47/2.48      | ~ m1_pre_topc(X1,X4)
% 15.47/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.47/2.48      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 15.47/2.48      | ~ v2_pre_topc(X2)
% 15.47/2.48      | ~ v2_pre_topc(X4)
% 15.47/2.48      | v2_struct_0(X4)
% 15.47/2.48      | v2_struct_0(X2)
% 15.47/2.48      | ~ l1_pre_topc(X4)
% 15.47/2.48      | ~ l1_pre_topc(X2)
% 15.47/2.48      | ~ v1_funct_1(X0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f73]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_935,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 15.47/2.48      | ~ m1_pre_topc(X0_59,X2_59)
% 15.47/2.48      | ~ m1_pre_topc(X3_59,X2_59)
% 15.47/2.48      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 15.47/2.48      | m1_subset_1(k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_59),u1_struct_0(X1_59))))
% 15.47/2.48      | ~ v2_pre_topc(X1_59)
% 15.47/2.48      | ~ v2_pre_topc(X2_59)
% 15.47/2.48      | v2_struct_0(X2_59)
% 15.47/2.48      | v2_struct_0(X1_59)
% 15.47/2.48      | ~ l1_pre_topc(X1_59)
% 15.47/2.48      | ~ l1_pre_topc(X2_59)
% 15.47/2.48      | ~ v1_funct_1(X0_55) ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_15]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1848,plain,
% 15.47/2.48      ( v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
% 15.47/2.48      | m1_pre_topc(X0_59,X2_59) != iProver_top
% 15.47/2.48      | m1_pre_topc(X3_59,X2_59) != iProver_top
% 15.47/2.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
% 15.47/2.48      | m1_subset_1(k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_59),u1_struct_0(X1_59)))) = iProver_top
% 15.47/2.48      | v2_pre_topc(X1_59) != iProver_top
% 15.47/2.48      | v2_pre_topc(X2_59) != iProver_top
% 15.47/2.48      | v2_struct_0(X1_59) = iProver_top
% 15.47/2.48      | v2_struct_0(X2_59) = iProver_top
% 15.47/2.48      | l1_pre_topc(X1_59) != iProver_top
% 15.47/2.48      | l1_pre_topc(X2_59) != iProver_top
% 15.47/2.48      | v1_funct_1(X0_55) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_935]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_27,negated_conjecture,
% 15.47/2.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 15.47/2.48      inference(cnf_transformation,[],[f91]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_924,negated_conjecture,
% 15.47/2.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_27]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1858,plain,
% 15.47/2.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_924]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5,plain,
% 15.47/2.48      ( ~ r2_funct_2(X0,X1,X2,X3)
% 15.47/2.48      | ~ v1_funct_2(X3,X0,X1)
% 15.47/2.48      | ~ v1_funct_2(X2,X0,X1)
% 15.47/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.47/2.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.47/2.48      | ~ v1_funct_1(X2)
% 15.47/2.48      | ~ v1_funct_1(X3)
% 15.47/2.48      | X3 = X2 ),
% 15.47/2.48      inference(cnf_transformation,[],[f60]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_942,plain,
% 15.47/2.48      ( ~ r2_funct_2(X0_58,X1_58,X0_55,X1_55)
% 15.47/2.48      | ~ v1_funct_2(X1_55,X0_58,X1_58)
% 15.47/2.48      | ~ v1_funct_2(X0_55,X0_58,X1_58)
% 15.47/2.48      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
% 15.47/2.48      | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
% 15.47/2.48      | ~ v1_funct_1(X0_55)
% 15.47/2.48      | ~ v1_funct_1(X1_55)
% 15.47/2.48      | X1_55 = X0_55 ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_5]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1841,plain,
% 15.47/2.48      ( X0_55 = X1_55
% 15.47/2.48      | r2_funct_2(X0_58,X1_58,X1_55,X0_55) != iProver_top
% 15.47/2.48      | v1_funct_2(X1_55,X0_58,X1_58) != iProver_top
% 15.47/2.48      | v1_funct_2(X0_55,X0_58,X1_58) != iProver_top
% 15.47/2.48      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 15.47/2.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 15.47/2.48      | v1_funct_1(X1_55) != iProver_top
% 15.47/2.48      | v1_funct_1(X0_55) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_942]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2927,plain,
% 15.47/2.48      ( sK5 = X0_55
% 15.47/2.48      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,sK5) != iProver_top
% 15.47/2.48      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.48      | v1_funct_1(X0_55) != iProver_top
% 15.47/2.48      | v1_funct_1(sK5) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1858,c_1841]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_29,negated_conjecture,
% 15.47/2.48      ( v1_funct_1(sK5) ),
% 15.47/2.48      inference(cnf_transformation,[],[f89]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_56,plain,
% 15.47/2.48      ( v1_funct_1(sK5) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_28,negated_conjecture,
% 15.47/2.48      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 15.47/2.48      inference(cnf_transformation,[],[f90]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_57,plain,
% 15.47/2.48      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3311,plain,
% 15.47/2.48      ( v1_funct_1(X0_55) != iProver_top
% 15.47/2.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.48      | sK5 = X0_55
% 15.47/2.48      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,sK5) != iProver_top
% 15.47/2.48      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_2927,c_56,c_57]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3312,plain,
% 15.47/2.48      ( sK5 = X0_55
% 15.47/2.48      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,sK5) != iProver_top
% 15.47/2.48      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.48      | v1_funct_1(X0_55) != iProver_top ),
% 15.47/2.48      inference(renaming,[status(thm)],[c_3311]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3664,plain,
% 15.47/2.48      ( k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55) = sK5
% 15.47/2.48      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55),sK5) != iProver_top
% 15.47/2.48      | v1_funct_2(X0_55,u1_struct_0(X1_59),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | v1_funct_2(k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 15.47/2.48      | m1_pre_topc(sK2,X0_59) != iProver_top
% 15.47/2.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_59),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.48      | v2_pre_topc(X0_59) != iProver_top
% 15.47/2.48      | v2_pre_topc(sK1) != iProver_top
% 15.47/2.48      | v2_struct_0(X0_59) = iProver_top
% 15.47/2.48      | v2_struct_0(sK1) = iProver_top
% 15.47/2.48      | l1_pre_topc(X0_59) != iProver_top
% 15.47/2.48      | l1_pre_topc(sK1) != iProver_top
% 15.47/2.48      | v1_funct_1(X0_55) != iProver_top
% 15.47/2.48      | v1_funct_1(k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55)) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1848,c_3312]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_7093,plain,
% 15.47/2.48      ( l1_pre_topc(X0_59) != iProver_top
% 15.47/2.48      | v2_pre_topc(X0_59) != iProver_top
% 15.47/2.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_59),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.48      | m1_pre_topc(sK2,X0_59) != iProver_top
% 15.47/2.48      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 15.47/2.48      | v1_funct_2(k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | v1_funct_2(X0_55,u1_struct_0(X1_59),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55),sK5) != iProver_top
% 15.47/2.48      | k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55) = sK5
% 15.47/2.48      | v2_struct_0(X0_59) = iProver_top
% 15.47/2.48      | v1_funct_1(X0_55) != iProver_top
% 15.47/2.48      | v1_funct_1(k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55)) != iProver_top ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_3664,c_46,c_47,c_48]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_7094,plain,
% 15.47/2.48      ( k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55) = sK5
% 15.47/2.48      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55),sK5) != iProver_top
% 15.47/2.48      | v1_funct_2(X0_55,u1_struct_0(X1_59),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | v1_funct_2(k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 15.47/2.48      | m1_pre_topc(sK2,X0_59) != iProver_top
% 15.47/2.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_59),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.48      | v2_pre_topc(X0_59) != iProver_top
% 15.47/2.48      | v2_struct_0(X0_59) = iProver_top
% 15.47/2.48      | l1_pre_topc(X0_59) != iProver_top
% 15.47/2.48      | v1_funct_1(X0_55) != iProver_top
% 15.47/2.48      | v1_funct_1(k3_tmap_1(X0_59,sK1,X1_59,sK2,X0_55)) != iProver_top ),
% 15.47/2.48      inference(renaming,[status(thm)],[c_7093]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_7097,plain,
% 15.47/2.48      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = sK5
% 15.47/2.48      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top
% 15.47/2.48      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.47/2.48      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.47/2.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.48      | v2_pre_topc(sK0) != iProver_top
% 15.47/2.48      | v2_struct_0(sK0) = iProver_top
% 15.47/2.48      | l1_pre_topc(sK0) != iProver_top
% 15.47/2.48      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top
% 15.47/2.48      | v1_funct_1(sK4) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_5295,c_7094]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_16,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.47/2.48      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 15.47/2.48      | ~ m1_pre_topc(X4,X3)
% 15.47/2.48      | ~ m1_pre_topc(X1,X3)
% 15.47/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.47/2.48      | ~ v2_pre_topc(X2)
% 15.47/2.48      | ~ v2_pre_topc(X3)
% 15.47/2.48      | v2_struct_0(X3)
% 15.47/2.48      | v2_struct_0(X2)
% 15.47/2.48      | ~ l1_pre_topc(X3)
% 15.47/2.48      | ~ l1_pre_topc(X2)
% 15.47/2.48      | ~ v1_funct_1(X0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f72]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_934,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 15.47/2.48      | v1_funct_2(k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55),u1_struct_0(X3_59),u1_struct_0(X1_59))
% 15.47/2.48      | ~ m1_pre_topc(X3_59,X2_59)
% 15.47/2.48      | ~ m1_pre_topc(X0_59,X2_59)
% 15.47/2.48      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 15.47/2.48      | ~ v2_pre_topc(X1_59)
% 15.47/2.48      | ~ v2_pre_topc(X2_59)
% 15.47/2.48      | v2_struct_0(X1_59)
% 15.47/2.48      | v2_struct_0(X2_59)
% 15.47/2.48      | ~ l1_pre_topc(X1_59)
% 15.47/2.48      | ~ l1_pre_topc(X2_59)
% 15.47/2.48      | ~ v1_funct_1(X0_55) ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_16]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2242,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 15.47/2.48      | v1_funct_2(k3_tmap_1(sK0,X1_59,X0_59,sK2,X0_55),u1_struct_0(sK2),u1_struct_0(X1_59))
% 15.47/2.48      | ~ m1_pre_topc(X0_59,sK0)
% 15.47/2.48      | ~ m1_pre_topc(sK2,sK0)
% 15.47/2.48      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 15.47/2.48      | ~ v2_pre_topc(X1_59)
% 15.47/2.48      | ~ v2_pre_topc(sK0)
% 15.47/2.48      | v2_struct_0(X1_59)
% 15.47/2.48      | v2_struct_0(sK0)
% 15.47/2.48      | ~ l1_pre_topc(X1_59)
% 15.47/2.48      | ~ l1_pre_topc(sK0)
% 15.47/2.48      | ~ v1_funct_1(X0_55) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_934]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2509,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(X0_59))
% 15.47/2.48      | v1_funct_2(k3_tmap_1(sK0,X0_59,sK0,sK2,X0_55),u1_struct_0(sK2),u1_struct_0(X0_59))
% 15.47/2.48      | ~ m1_pre_topc(sK0,sK0)
% 15.47/2.48      | ~ m1_pre_topc(sK2,sK0)
% 15.47/2.48      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_59))))
% 15.47/2.48      | ~ v2_pre_topc(X0_59)
% 15.47/2.48      | ~ v2_pre_topc(sK0)
% 15.47/2.48      | v2_struct_0(X0_59)
% 15.47/2.48      | v2_struct_0(sK0)
% 15.47/2.48      | ~ l1_pre_topc(X0_59)
% 15.47/2.48      | ~ l1_pre_topc(sK0)
% 15.47/2.48      | ~ v1_funct_1(X0_55) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_2242]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3201,plain,
% 15.47/2.48      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.47/2.48      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 15.47/2.48      | ~ m1_pre_topc(sK0,sK0)
% 15.47/2.48      | ~ m1_pre_topc(sK2,sK0)
% 15.47/2.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 15.47/2.48      | ~ v2_pre_topc(sK0)
% 15.47/2.48      | ~ v2_pre_topc(sK1)
% 15.47/2.48      | v2_struct_0(sK0)
% 15.47/2.48      | v2_struct_0(sK1)
% 15.47/2.48      | ~ l1_pre_topc(sK0)
% 15.47/2.48      | ~ l1_pre_topc(sK1)
% 15.47/2.48      | ~ v1_funct_1(sK4) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_2509]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3202,plain,
% 15.47/2.48      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 15.47/2.48      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.47/2.48      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.47/2.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.48      | v2_pre_topc(sK0) != iProver_top
% 15.47/2.48      | v2_pre_topc(sK1) != iProver_top
% 15.47/2.48      | v2_struct_0(sK0) = iProver_top
% 15.47/2.48      | v2_struct_0(sK1) = iProver_top
% 15.47/2.48      | l1_pre_topc(sK0) != iProver_top
% 15.47/2.48      | l1_pre_topc(sK1) != iProver_top
% 15.47/2.48      | v1_funct_1(sK4) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_3201]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_17,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.47/2.48      | ~ m1_pre_topc(X3,X4)
% 15.47/2.48      | ~ m1_pre_topc(X1,X4)
% 15.47/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.47/2.48      | ~ v2_pre_topc(X2)
% 15.47/2.48      | ~ v2_pre_topc(X4)
% 15.47/2.48      | v2_struct_0(X4)
% 15.47/2.48      | v2_struct_0(X2)
% 15.47/2.48      | ~ l1_pre_topc(X4)
% 15.47/2.48      | ~ l1_pre_topc(X2)
% 15.47/2.48      | ~ v1_funct_1(X0)
% 15.47/2.48      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 15.47/2.48      inference(cnf_transformation,[],[f71]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_933,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 15.47/2.48      | ~ m1_pre_topc(X0_59,X2_59)
% 15.47/2.48      | ~ m1_pre_topc(X3_59,X2_59)
% 15.47/2.48      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 15.47/2.48      | ~ v2_pre_topc(X1_59)
% 15.47/2.48      | ~ v2_pre_topc(X2_59)
% 15.47/2.48      | v2_struct_0(X2_59)
% 15.47/2.48      | v2_struct_0(X1_59)
% 15.47/2.48      | ~ l1_pre_topc(X1_59)
% 15.47/2.48      | ~ l1_pre_topc(X2_59)
% 15.47/2.48      | ~ v1_funct_1(X0_55)
% 15.47/2.48      | v1_funct_1(k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55)) ),
% 15.47/2.48      inference(subtyping,[status(esa)],[c_17]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1954,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 15.47/2.48      | ~ m1_pre_topc(X0_59,sK0)
% 15.47/2.48      | ~ m1_pre_topc(X2_59,sK0)
% 15.47/2.48      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 15.47/2.48      | ~ v2_pre_topc(X1_59)
% 15.47/2.48      | ~ v2_pre_topc(sK0)
% 15.47/2.48      | v2_struct_0(X1_59)
% 15.47/2.48      | v2_struct_0(sK0)
% 15.47/2.48      | ~ l1_pre_topc(X1_59)
% 15.47/2.48      | ~ l1_pre_topc(sK0)
% 15.47/2.48      | ~ v1_funct_1(X0_55)
% 15.47/2.48      | v1_funct_1(k3_tmap_1(sK0,X1_59,X0_59,X2_59,X0_55)) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_933]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2516,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(X0_59))
% 15.47/2.48      | ~ m1_pre_topc(X1_59,sK0)
% 15.47/2.48      | ~ m1_pre_topc(sK0,sK0)
% 15.47/2.48      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_59))))
% 15.47/2.48      | ~ v2_pre_topc(X0_59)
% 15.47/2.48      | ~ v2_pre_topc(sK0)
% 15.47/2.48      | v2_struct_0(X0_59)
% 15.47/2.48      | v2_struct_0(sK0)
% 15.47/2.48      | ~ l1_pre_topc(X0_59)
% 15.47/2.48      | ~ l1_pre_topc(sK0)
% 15.47/2.48      | ~ v1_funct_1(X0_55)
% 15.47/2.48      | v1_funct_1(k3_tmap_1(sK0,X0_59,sK0,X1_59,X0_55)) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_1954]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3234,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(X0_59))
% 15.47/2.48      | ~ m1_pre_topc(sK0,sK0)
% 15.47/2.48      | ~ m1_pre_topc(sK2,sK0)
% 15.47/2.48      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_59))))
% 15.47/2.48      | ~ v2_pre_topc(X0_59)
% 15.47/2.48      | ~ v2_pre_topc(sK0)
% 15.47/2.48      | v2_struct_0(X0_59)
% 15.47/2.48      | v2_struct_0(sK0)
% 15.47/2.48      | ~ l1_pre_topc(X0_59)
% 15.47/2.48      | ~ l1_pre_topc(sK0)
% 15.47/2.48      | ~ v1_funct_1(X0_55)
% 15.47/2.48      | v1_funct_1(k3_tmap_1(sK0,X0_59,sK0,sK2,X0_55)) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_2516]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3841,plain,
% 15.47/2.48      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 15.47/2.48      | ~ m1_pre_topc(sK0,sK0)
% 15.47/2.48      | ~ m1_pre_topc(sK2,sK0)
% 15.47/2.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 15.47/2.48      | ~ v2_pre_topc(sK0)
% 15.47/2.48      | ~ v2_pre_topc(sK1)
% 15.47/2.48      | v2_struct_0(sK0)
% 15.47/2.48      | v2_struct_0(sK1)
% 15.47/2.48      | ~ l1_pre_topc(sK0)
% 15.47/2.48      | ~ l1_pre_topc(sK1)
% 15.47/2.48      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
% 15.47/2.48      | ~ v1_funct_1(sK4) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_3234]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3842,plain,
% 15.47/2.48      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.48      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.47/2.48      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.47/2.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.48      | v2_pre_topc(sK0) != iProver_top
% 15.47/2.48      | v2_pre_topc(sK1) != iProver_top
% 15.47/2.48      | v2_struct_0(sK0) = iProver_top
% 15.47/2.48      | v2_struct_0(sK1) = iProver_top
% 15.47/2.48      | l1_pre_topc(sK0) != iProver_top
% 15.47/2.48      | l1_pre_topc(sK1) != iProver_top
% 15.47/2.48      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) = iProver_top
% 15.47/2.48      | v1_funct_1(sK4) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_3841]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_7100,plain,
% 15.47/2.48      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = sK5
% 15.47/2.48      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.49                [c_7097,c_43,c_44,c_45,c_46,c_47,c_48,c_50,c_53,c_54,
% 15.47/2.49                 c_55,c_1876,c_3202,c_3842]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_5302,plain,
% 15.47/2.49      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 15.47/2.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.49      | l1_struct_0(sK0) != iProver_top
% 15.47/2.49      | l1_struct_0(sK1) != iProver_top
% 15.47/2.49      | l1_struct_0(sK2) != iProver_top
% 15.47/2.49      | v1_funct_1(sK4) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_5204,c_1845]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_7,plain,
% 15.47/2.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 15.47/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_940,plain,
% 15.47/2.49      ( ~ m1_pre_topc(X0_59,X1_59)
% 15.47/2.49      | ~ l1_pre_topc(X1_59)
% 15.47/2.49      | l1_pre_topc(X0_59) ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_7]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_1843,plain,
% 15.47/2.49      ( m1_pre_topc(X0_59,X1_59) != iProver_top
% 15.47/2.49      | l1_pre_topc(X1_59) != iProver_top
% 15.47/2.49      | l1_pre_topc(X0_59) = iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_940]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_2464,plain,
% 15.47/2.49      ( l1_pre_topc(sK0) != iProver_top
% 15.47/2.49      | l1_pre_topc(sK2) = iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_1866,c_1843]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_2765,plain,
% 15.47/2.49      ( l1_pre_topc(sK2) = iProver_top ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_2464,c_45]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_2769,plain,
% 15.47/2.49      ( l1_struct_0(sK2) = iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_2765,c_1842]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_5713,plain,
% 15.47/2.49      ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_5302,c_48,c_53,c_54,c_55,c_102,c_2460,c_2769]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_5725,plain,
% 15.47/2.49      ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK5
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top
% 15.47/2.49      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_5713,c_3312]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_1846,plain,
% 15.47/2.49      ( v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
% 15.47/2.49      | v1_funct_2(k2_tmap_1(X0_59,X1_59,X0_55,X2_59),u1_struct_0(X2_59),u1_struct_0(X1_59)) = iProver_top
% 15.47/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
% 15.47/2.49      | l1_struct_0(X1_59) != iProver_top
% 15.47/2.49      | l1_struct_0(X2_59) != iProver_top
% 15.47/2.49      | l1_struct_0(X0_59) != iProver_top
% 15.47/2.49      | v1_funct_1(X0_55) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_937]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_5303,plain,
% 15.47/2.49      ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 15.47/2.49      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.49      | l1_struct_0(sK0) != iProver_top
% 15.47/2.49      | l1_struct_0(sK1) != iProver_top
% 15.47/2.49      | l1_struct_0(sK2) != iProver_top
% 15.47/2.49      | v1_funct_1(sK4) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_5204,c_1846]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_5304,plain,
% 15.47/2.49      ( l1_struct_0(sK2) != iProver_top
% 15.47/2.49      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_5204,c_3254]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_5815,plain,
% 15.47/2.49      ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK5
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_5725,c_48,c_53,c_54,c_55,c_102,c_2460,c_2769,c_5303,
% 15.47/2.49                 c_5304]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_7104,plain,
% 15.47/2.49      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = sK5
% 15.47/2.49      | k7_relat_1(sK4,u1_struct_0(sK2)) = sK5 ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_7100,c_5815]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_3659,plain,
% 15.47/2.49      ( k2_partfun1(u1_struct_0(X0_59),u1_struct_0(X1_59),k3_tmap_1(X2_59,X1_59,X3_59,X0_59,X0_55),X0_58) = k7_relat_1(k3_tmap_1(X2_59,X1_59,X3_59,X0_59,X0_55),X0_58)
% 15.47/2.49      | v1_funct_2(X0_55,u1_struct_0(X3_59),u1_struct_0(X1_59)) != iProver_top
% 15.47/2.49      | m1_pre_topc(X3_59,X2_59) != iProver_top
% 15.47/2.49      | m1_pre_topc(X0_59,X2_59) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_59),u1_struct_0(X1_59)))) != iProver_top
% 15.47/2.49      | v2_pre_topc(X1_59) != iProver_top
% 15.47/2.49      | v2_pre_topc(X2_59) != iProver_top
% 15.47/2.49      | v2_struct_0(X1_59) = iProver_top
% 15.47/2.49      | v2_struct_0(X2_59) = iProver_top
% 15.47/2.49      | l1_pre_topc(X1_59) != iProver_top
% 15.47/2.49      | l1_pre_topc(X2_59) != iProver_top
% 15.47/2.49      | v1_funct_1(X0_55) != iProver_top
% 15.47/2.49      | v1_funct_1(k3_tmap_1(X2_59,X1_59,X3_59,X0_59,X0_55)) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_1848,c_1839]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_10812,plain,
% 15.47/2.49      ( k2_partfun1(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4),X0_58) = k7_relat_1(k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4),X0_58)
% 15.47/2.49      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | m1_pre_topc(X0_59,X1_59) != iProver_top
% 15.47/2.49      | m1_pre_topc(sK0,X1_59) != iProver_top
% 15.47/2.49      | v2_pre_topc(X1_59) != iProver_top
% 15.47/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.47/2.49      | v2_struct_0(X1_59) = iProver_top
% 15.47/2.49      | v2_struct_0(sK1) = iProver_top
% 15.47/2.49      | l1_pre_topc(X1_59) != iProver_top
% 15.47/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.47/2.49      | v1_funct_1(k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4)) != iProver_top
% 15.47/2.49      | v1_funct_1(sK4) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_1879,c_3659]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_1850,plain,
% 15.47/2.49      ( v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
% 15.47/2.49      | m1_pre_topc(X0_59,X2_59) != iProver_top
% 15.47/2.49      | m1_pre_topc(X3_59,X2_59) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
% 15.47/2.49      | v2_pre_topc(X1_59) != iProver_top
% 15.47/2.49      | v2_pre_topc(X2_59) != iProver_top
% 15.47/2.49      | v2_struct_0(X1_59) = iProver_top
% 15.47/2.49      | v2_struct_0(X2_59) = iProver_top
% 15.47/2.49      | l1_pre_topc(X1_59) != iProver_top
% 15.47/2.49      | l1_pre_topc(X2_59) != iProver_top
% 15.47/2.49      | v1_funct_1(X0_55) != iProver_top
% 15.47/2.49      | v1_funct_1(k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55)) = iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_933]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_3161,plain,
% 15.47/2.49      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | m1_pre_topc(X0_59,X1_59) != iProver_top
% 15.47/2.49      | m1_pre_topc(sK0,X1_59) != iProver_top
% 15.47/2.49      | v2_pre_topc(X1_59) != iProver_top
% 15.47/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.47/2.49      | v2_struct_0(X1_59) = iProver_top
% 15.47/2.49      | v2_struct_0(sK1) = iProver_top
% 15.47/2.49      | l1_pre_topc(X1_59) != iProver_top
% 15.47/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.47/2.49      | v1_funct_1(k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4)) = iProver_top
% 15.47/2.49      | v1_funct_1(sK4) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_1879,c_1850]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_3439,plain,
% 15.47/2.49      ( v1_funct_1(k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4)) = iProver_top
% 15.47/2.49      | v2_struct_0(X1_59) = iProver_top
% 15.47/2.49      | m1_pre_topc(X0_59,X1_59) != iProver_top
% 15.47/2.49      | m1_pre_topc(sK0,X1_59) != iProver_top
% 15.47/2.49      | v2_pre_topc(X1_59) != iProver_top
% 15.47/2.49      | l1_pre_topc(X1_59) != iProver_top ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_3161,c_46,c_47,c_48,c_53,c_54]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_3440,plain,
% 15.47/2.49      ( m1_pre_topc(X0_59,X1_59) != iProver_top
% 15.47/2.49      | m1_pre_topc(sK0,X1_59) != iProver_top
% 15.47/2.49      | v2_pre_topc(X1_59) != iProver_top
% 15.47/2.49      | v2_struct_0(X1_59) = iProver_top
% 15.47/2.49      | l1_pre_topc(X1_59) != iProver_top
% 15.47/2.49      | v1_funct_1(k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4)) = iProver_top ),
% 15.47/2.49      inference(renaming,[status(thm)],[c_3439]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_11337,plain,
% 15.47/2.49      ( l1_pre_topc(X1_59) != iProver_top
% 15.47/2.49      | v2_pre_topc(X1_59) != iProver_top
% 15.47/2.49      | m1_pre_topc(sK0,X1_59) != iProver_top
% 15.47/2.49      | m1_pre_topc(X0_59,X1_59) != iProver_top
% 15.47/2.49      | k2_partfun1(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4),X0_58) = k7_relat_1(k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4),X0_58)
% 15.47/2.49      | v2_struct_0(X1_59) = iProver_top ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_10812,c_46,c_47,c_48,c_53,c_54,c_3440]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_11338,plain,
% 15.47/2.49      ( k2_partfun1(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4),X0_58) = k7_relat_1(k3_tmap_1(X1_59,sK1,sK0,X0_59,sK4),X0_58)
% 15.47/2.49      | m1_pre_topc(X0_59,X1_59) != iProver_top
% 15.47/2.49      | m1_pre_topc(sK0,X1_59) != iProver_top
% 15.47/2.49      | v2_pre_topc(X1_59) != iProver_top
% 15.47/2.49      | v2_struct_0(X1_59) = iProver_top
% 15.47/2.49      | l1_pre_topc(X1_59) != iProver_top ),
% 15.47/2.49      inference(renaming,[status(thm)],[c_11337]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_11343,plain,
% 15.47/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),X0_58) = k7_relat_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),X0_58)
% 15.47/2.49      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.47/2.49      | v2_pre_topc(sK0) != iProver_top
% 15.47/2.49      | v2_struct_0(sK0) = iProver_top
% 15.47/2.49      | l1_pre_topc(sK0) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_1866,c_11338]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_11396,plain,
% 15.47/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),X0_58) = k7_relat_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),X0_58) ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_11343,c_43,c_44,c_45,c_1876]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_23672,plain,
% 15.47/2.49      ( k7_relat_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),X0_58) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,X0_58)
% 15.47/2.49      | k7_relat_1(sK4,u1_struct_0(sK2)) = sK5 ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_7104,c_11396]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_2272,plain,
% 15.47/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,X0_58) = k7_relat_1(sK5,X0_58)
% 15.47/2.49      | v1_funct_1(sK5) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_1858,c_1839]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_2448,plain,
% 15.47/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,X0_58) = k7_relat_1(sK5,X0_58) ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_2272,c_56]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_23687,plain,
% 15.47/2.49      ( k7_relat_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),X0_58) = k7_relat_1(sK5,X0_58)
% 15.47/2.49      | k7_relat_1(sK4,u1_struct_0(sK2)) = sK5 ),
% 15.47/2.49      inference(light_normalisation,[status(thm)],[c_23672,c_2448]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_58,plain,
% 15.47/2.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_2453,plain,
% 15.47/2.49      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4) = iProver_top
% 15.47/2.49      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | v1_funct_1(sK4) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_1879,c_1840]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_5718,plain,
% 15.47/2.49      ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 15.47/2.49      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.49      | v1_funct_1(X0_55) != iProver_top
% 15.47/2.49      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_5713,c_1841]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_6548,plain,
% 15.47/2.49      ( v1_funct_1(X0_55) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.49      | k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 15.47/2.49      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_5718,c_48,c_53,c_54,c_55,c_102,c_2460,c_2769,c_5303,
% 15.47/2.49                 c_5304]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_6549,plain,
% 15.47/2.49      ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 15.47/2.49      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.49      | v1_funct_1(X0_55) != iProver_top ),
% 15.47/2.49      inference(renaming,[status(thm)],[c_6548]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_6551,plain,
% 15.47/2.49      ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK5
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 15.47/2.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.49      | v1_funct_1(sK5) != iProver_top ),
% 15.47/2.49      inference(instantiation,[status(thm)],[c_6549]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_5508,plain,
% 15.47/2.49      ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_59,X0_55),k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_55,sK4) != iProver_top
% 15.47/2.49      | v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | m1_pre_topc(X0_59,sK0) != iProver_top
% 15.47/2.49      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.49      | v2_pre_topc(sK0) != iProver_top
% 15.47/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_59) = iProver_top
% 15.47/2.49      | v2_struct_0(sK0) = iProver_top
% 15.47/2.49      | v2_struct_0(sK1) = iProver_top
% 15.47/2.49      | l1_pre_topc(sK0) != iProver_top
% 15.47/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.47/2.49      | v1_funct_1(X0_55) != iProver_top
% 15.47/2.49      | v1_funct_1(sK4) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_5206,c_1851]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_20495,plain,
% 15.47/2.49      ( v1_funct_1(X0_55) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_59) = iProver_top
% 15.47/2.49      | m1_pre_topc(X0_59,sK0) != iProver_top
% 15.47/2.49      | r2_funct_2(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_59,X0_55),k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_55,sK4) != iProver_top
% 15.47/2.49      | v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_5508,c_43,c_44,c_45,c_46,c_47,c_48,c_53,c_54,c_55,
% 15.47/2.49                 c_1876]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_20496,plain,
% 15.47/2.49      ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_59,X0_55),k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_55,sK4) != iProver_top
% 15.47/2.49      | v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | m1_pre_topc(X0_59,sK0) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_59) = iProver_top
% 15.47/2.49      | v1_funct_1(X0_55) != iProver_top ),
% 15.47/2.49      inference(renaming,[status(thm)],[c_20495]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_20501,plain,
% 15.47/2.49      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_55,sK4) != iProver_top
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,X0_55),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
% 15.47/2.49      | v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.49      | v2_struct_0(sK2) = iProver_top
% 15.47/2.49      | v1_funct_1(X0_55) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_5204,c_20496]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_20606,plain,
% 15.47/2.49      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_55,sK4) != iProver_top
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,X0_55),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
% 15.47/2.49      | v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | v1_funct_1(X0_55) != iProver_top ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_20501,c_49,c_50]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_20607,plain,
% 15.47/2.49      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_55,sK4) != iProver_top
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,X0_55),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
% 15.47/2.49      | v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.49      | v1_funct_1(X0_55) != iProver_top ),
% 15.47/2.49      inference(renaming,[status(thm)],[c_20606]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_23678,plain,
% 15.47/2.49      ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK5
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4) != iProver_top
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
% 15.47/2.49      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.47/2.49      | v1_funct_1(sK4) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_7104,c_20607]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_24078,plain,
% 15.47/2.49      ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK5 ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_23687,c_53,c_54,c_55,c_56,c_57,c_58,c_2453,c_6551,
% 15.47/2.49                 c_23678]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_24392,plain,
% 15.47/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_59,sK2,k2_tmap_1(sK0,sK1,sK4,X0_59)),sK5) = iProver_top
% 15.47/2.49      | m1_pre_topc(X0_59,sK0) != iProver_top
% 15.47/2.49      | m1_pre_topc(sK2,X0_59) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_59) = iProver_top
% 15.47/2.49      | l1_struct_0(X0_59) != iProver_top ),
% 15.47/2.49      inference(light_normalisation,[status(thm)],[c_24387,c_24078]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_24397,plain,
% 15.47/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
% 15.47/2.49      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.47/2.49      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.47/2.49      | v2_struct_0(sK0) = iProver_top
% 15.47/2.49      | l1_struct_0(sK0) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_5206,c_24392]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_20,negated_conjecture,
% 15.47/2.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 15.47/2.49      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 15.47/2.49      inference(cnf_transformation,[],[f98]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_930,negated_conjecture,
% 15.47/2.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 15.47/2.49      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_20]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_1853,plain,
% 15.47/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) != iProver_top
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_930]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_1881,plain,
% 15.47/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
% 15.47/2.49      inference(light_normalisation,[status(thm)],[c_1853,c_907,c_928]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_5296,plain,
% 15.47/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top ),
% 15.47/2.49      inference(demodulation,[status(thm)],[c_5204,c_1881]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_24114,plain,
% 15.47/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
% 15.47/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) != iProver_top ),
% 15.47/2.49      inference(demodulation,[status(thm)],[c_24078,c_5296]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_2452,plain,
% 15.47/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) = iProver_top
% 15.47/2.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.47/2.49      | v1_funct_1(sK5) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_1858,c_1840]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(contradiction,plain,
% 15.47/2.49      ( $false ),
% 15.47/2.49      inference(minisat,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_24397,c_24114,c_2460,c_2452,c_1876,c_57,c_56,c_50,
% 15.47/2.49                 c_43]) ).
% 15.47/2.49  
% 15.47/2.49  
% 15.47/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.47/2.49  
% 15.47/2.49  ------                               Statistics
% 15.47/2.49  
% 15.47/2.49  ------ General
% 15.47/2.49  
% 15.47/2.49  abstr_ref_over_cycles:                  0
% 15.47/2.49  abstr_ref_under_cycles:                 0
% 15.47/2.49  gc_basic_clause_elim:                   0
% 15.47/2.49  forced_gc_time:                         0
% 15.47/2.49  parsing_time:                           0.013
% 15.47/2.49  unif_index_cands_time:                  0.
% 15.47/2.49  unif_index_add_time:                    0.
% 15.47/2.49  orderings_time:                         0.
% 15.47/2.49  out_proof_time:                         0.031
% 15.47/2.49  total_time:                             1.506
% 15.47/2.49  num_of_symbols:                         60
% 15.47/2.49  num_of_terms:                           28824
% 15.47/2.49  
% 15.47/2.49  ------ Preprocessing
% 15.47/2.49  
% 15.47/2.49  num_of_splits:                          0
% 15.47/2.49  num_of_split_atoms:                     0
% 15.47/2.49  num_of_reused_defs:                     0
% 15.47/2.49  num_eq_ax_congr_red:                    15
% 15.47/2.49  num_of_sem_filtered_clauses:            1
% 15.47/2.49  num_of_subtypes:                        5
% 15.47/2.49  monotx_restored_types:                  0
% 15.47/2.49  sat_num_of_epr_types:                   0
% 15.47/2.49  sat_num_of_non_cyclic_types:            0
% 15.47/2.49  sat_guarded_non_collapsed_types:        1
% 15.47/2.49  num_pure_diseq_elim:                    0
% 15.47/2.49  simp_replaced_by:                       0
% 15.47/2.49  res_preprocessed:                       200
% 15.47/2.49  prep_upred:                             0
% 15.47/2.49  prep_unflattend:                        12
% 15.47/2.49  smt_new_axioms:                         0
% 15.47/2.49  pred_elim_cands:                        9
% 15.47/2.49  pred_elim:                              4
% 15.47/2.49  pred_elim_cl:                           5
% 15.47/2.49  pred_elim_cycles:                       6
% 15.47/2.49  merged_defs:                            8
% 15.47/2.49  merged_defs_ncl:                        0
% 15.47/2.49  bin_hyper_res:                          8
% 15.47/2.49  prep_cycles:                            4
% 15.47/2.49  pred_elim_time:                         0.003
% 15.47/2.49  splitting_time:                         0.
% 15.47/2.49  sem_filter_time:                        0.
% 15.47/2.49  monotx_time:                            0.
% 15.47/2.49  subtype_inf_time:                       0.001
% 15.47/2.49  
% 15.47/2.49  ------ Problem properties
% 15.47/2.49  
% 15.47/2.49  clauses:                                38
% 15.47/2.49  conjectures:                            22
% 15.47/2.49  epr:                                    18
% 15.47/2.49  horn:                                   32
% 15.47/2.49  ground:                                 23
% 15.47/2.49  unary:                                  21
% 15.47/2.49  binary:                                 4
% 15.47/2.49  lits:                                   139
% 15.47/2.49  lits_eq:                                6
% 15.47/2.49  fd_pure:                                0
% 15.47/2.49  fd_pseudo:                              0
% 15.47/2.49  fd_cond:                                0
% 15.47/2.49  fd_pseudo_cond:                         1
% 15.47/2.49  ac_symbols:                             0
% 15.47/2.49  
% 15.47/2.49  ------ Propositional Solver
% 15.47/2.49  
% 15.47/2.49  prop_solver_calls:                      35
% 15.47/2.49  prop_fast_solver_calls:                 3717
% 15.47/2.49  smt_solver_calls:                       0
% 15.47/2.49  smt_fast_solver_calls:                  0
% 15.47/2.49  prop_num_of_clauses:                    12351
% 15.47/2.49  prop_preprocess_simplified:             26537
% 15.47/2.49  prop_fo_subsumed:                       645
% 15.47/2.49  prop_solver_time:                       0.
% 15.47/2.49  smt_solver_time:                        0.
% 15.47/2.49  smt_fast_solver_time:                   0.
% 15.47/2.49  prop_fast_solver_time:                  0.
% 15.47/2.49  prop_unsat_core_time:                   0.003
% 15.47/2.49  
% 15.47/2.49  ------ QBF
% 15.47/2.49  
% 15.47/2.49  qbf_q_res:                              0
% 15.47/2.49  qbf_num_tautologies:                    0
% 15.47/2.49  qbf_prep_cycles:                        0
% 15.47/2.49  
% 15.47/2.49  ------ BMC1
% 15.47/2.49  
% 15.47/2.49  bmc1_current_bound:                     -1
% 15.47/2.49  bmc1_last_solved_bound:                 -1
% 15.47/2.49  bmc1_unsat_core_size:                   -1
% 15.47/2.49  bmc1_unsat_core_parents_size:           -1
% 15.47/2.49  bmc1_merge_next_fun:                    0
% 15.47/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.47/2.49  
% 15.47/2.49  ------ Instantiation
% 15.47/2.49  
% 15.47/2.49  inst_num_of_clauses:                    3744
% 15.47/2.49  inst_num_in_passive:                    2158
% 15.47/2.49  inst_num_in_active:                     1088
% 15.47/2.49  inst_num_in_unprocessed:                498
% 15.47/2.49  inst_num_of_loops:                      1300
% 15.47/2.49  inst_num_of_learning_restarts:          0
% 15.47/2.49  inst_num_moves_active_passive:          207
% 15.47/2.49  inst_lit_activity:                      0
% 15.47/2.49  inst_lit_activity_moves:                3
% 15.47/2.49  inst_num_tautologies:                   0
% 15.47/2.49  inst_num_prop_implied:                  0
% 15.47/2.49  inst_num_existing_simplified:           0
% 15.47/2.49  inst_num_eq_res_simplified:             0
% 15.47/2.49  inst_num_child_elim:                    0
% 15.47/2.49  inst_num_of_dismatching_blockings:      566
% 15.47/2.49  inst_num_of_non_proper_insts:           2873
% 15.47/2.49  inst_num_of_duplicates:                 0
% 15.47/2.49  inst_inst_num_from_inst_to_res:         0
% 15.47/2.49  inst_dismatching_checking_time:         0.
% 15.47/2.49  
% 15.47/2.49  ------ Resolution
% 15.47/2.49  
% 15.47/2.49  res_num_of_clauses:                     0
% 15.47/2.49  res_num_in_passive:                     0
% 15.47/2.49  res_num_in_active:                      0
% 15.47/2.49  res_num_of_loops:                       204
% 15.47/2.49  res_forward_subset_subsumed:            73
% 15.47/2.49  res_backward_subset_subsumed:           0
% 15.47/2.49  res_forward_subsumed:                   0
% 15.47/2.49  res_backward_subsumed:                  0
% 15.47/2.49  res_forward_subsumption_resolution:     0
% 15.47/2.49  res_backward_subsumption_resolution:    0
% 15.47/2.49  res_clause_to_clause_subsumption:       1134
% 15.47/2.49  res_orphan_elimination:                 0
% 15.47/2.49  res_tautology_del:                      61
% 15.47/2.49  res_num_eq_res_simplified:              0
% 15.47/2.49  res_num_sel_changes:                    0
% 15.47/2.49  res_moves_from_active_to_pass:          0
% 15.47/2.49  
% 15.47/2.49  ------ Superposition
% 15.47/2.49  
% 15.47/2.49  sup_time_total:                         0.
% 15.47/2.49  sup_time_generating:                    0.
% 15.47/2.49  sup_time_sim_full:                      0.
% 15.47/2.49  sup_time_sim_immed:                     0.
% 15.47/2.49  
% 15.47/2.49  sup_num_of_clauses:                     329
% 15.47/2.49  sup_num_in_active:                      198
% 15.47/2.49  sup_num_in_passive:                     131
% 15.47/2.49  sup_num_of_loops:                       258
% 15.47/2.49  sup_fw_superposition:                   291
% 15.47/2.49  sup_bw_superposition:                   199
% 15.47/2.49  sup_immediate_simplified:               158
% 15.47/2.49  sup_given_eliminated:                   6
% 15.47/2.49  comparisons_done:                       0
% 15.47/2.49  comparisons_avoided:                    0
% 15.47/2.49  
% 15.47/2.49  ------ Simplifications
% 15.47/2.49  
% 15.47/2.49  
% 15.47/2.49  sim_fw_subset_subsumed:                 20
% 15.47/2.49  sim_bw_subset_subsumed:                 18
% 15.47/2.49  sim_fw_subsumed:                        76
% 15.47/2.49  sim_bw_subsumed:                        13
% 15.47/2.49  sim_fw_subsumption_res:                 0
% 15.47/2.49  sim_bw_subsumption_res:                 0
% 15.47/2.49  sim_tautology_del:                      12
% 15.47/2.49  sim_eq_tautology_del:                   22
% 15.47/2.49  sim_eq_res_simp:                        0
% 15.47/2.49  sim_fw_demodulated:                     34
% 15.47/2.49  sim_bw_demodulated:                     45
% 15.47/2.49  sim_light_normalised:                   123
% 15.47/2.49  sim_joinable_taut:                      0
% 15.47/2.49  sim_joinable_simp:                      0
% 15.47/2.49  sim_ac_normalised:                      0
% 15.47/2.49  sim_smt_subsumption:                    0
% 15.47/2.49  
%------------------------------------------------------------------------------
