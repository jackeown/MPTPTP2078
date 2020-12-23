%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:07 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  228 (2167 expanded)
%              Number of clauses        :  159 ( 376 expanded)
%              Number of leaves         :   17 ( 987 expanded)
%              Depth                    :   27
%              Number of atoms          : 1919 (45855 expanded)
%              Number of equality atoms :  510 (3194 expanded)
%              Maximal formula depth    :   27 (   9 average)
%              Maximal clause size      :   48 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
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
                                          & m1_connsp_2(X5,X3,X6)
                                          & r1_tarski(X5,u1_struct_0(X2)) )
                                       => ( r1_tmap_1(X3,X1,X4,X6)
                                        <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & m1_connsp_2(X5,X3,X6)
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & m1_connsp_2(X5,X3,X6)
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
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
    inference(flattening,[],[f23])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X1,X4,X6) )
                                  & X6 = X7
                                  & m1_connsp_2(X5,X3,X6)
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
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
    inference(nnf_transformation,[],[f24])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X1,X4,X6) )
                                  & X6 = X7
                                  & m1_connsp_2(X5,X3,X6)
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
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
    inference(flattening,[],[f26])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
            | ~ r1_tmap_1(X3,X1,X4,X6) )
          & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
            | r1_tmap_1(X3,X1,X4,X6) )
          & X6 = X7
          & m1_connsp_2(X5,X3,X6)
          & r1_tarski(X5,u1_struct_0(X2))
          & m1_subset_1(X7,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7)
          | ~ r1_tmap_1(X3,X1,X4,X6) )
        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7)
          | r1_tmap_1(X3,X1,X4,X6) )
        & sK7 = X6
        & m1_connsp_2(X5,X3,X6)
        & r1_tarski(X5,u1_struct_0(X2))
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                | ~ r1_tmap_1(X3,X1,X4,X6) )
              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                | r1_tmap_1(X3,X1,X4,X6) )
              & X6 = X7
              & m1_connsp_2(X5,X3,X6)
              & r1_tarski(X5,u1_struct_0(X2))
              & m1_subset_1(X7,u1_struct_0(X2)) )
          & m1_subset_1(X6,u1_struct_0(X3)) )
     => ( ? [X7] :
            ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
              | ~ r1_tmap_1(X3,X1,X4,sK6) )
            & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
              | r1_tmap_1(X3,X1,X4,sK6) )
            & sK6 = X7
            & m1_connsp_2(X5,X3,sK6)
            & r1_tarski(X5,u1_struct_0(X2))
            & m1_subset_1(X7,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                  & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                    | r1_tmap_1(X3,X1,X4,X6) )
                  & X6 = X7
                  & m1_connsp_2(X5,X3,X6)
                  & r1_tarski(X5,u1_struct_0(X2))
                  & m1_subset_1(X7,u1_struct_0(X2)) )
              & m1_subset_1(X6,u1_struct_0(X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                  | ~ r1_tmap_1(X3,X1,X4,X6) )
                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                  | r1_tmap_1(X3,X1,X4,X6) )
                & X6 = X7
                & m1_connsp_2(sK5,X3,X6)
                & r1_tarski(sK5,u1_struct_0(X2))
                & m1_subset_1(X7,u1_struct_0(X2)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                        | ~ r1_tmap_1(X3,X1,X4,X6) )
                      & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                        | r1_tmap_1(X3,X1,X4,X6) )
                      & X6 = X7
                      & m1_connsp_2(X5,X3,X6)
                      & r1_tarski(X5,u1_struct_0(X2))
                      & m1_subset_1(X7,u1_struct_0(X2)) )
                  & m1_subset_1(X6,u1_struct_0(X3)) )
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X7)
                      | ~ r1_tmap_1(X3,X1,sK4,X6) )
                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X7)
                      | r1_tmap_1(X3,X1,sK4,X6) )
                    & X6 = X7
                    & m1_connsp_2(X5,X3,X6)
                    & r1_tarski(X5,u1_struct_0(X2))
                    & m1_subset_1(X7,u1_struct_0(X2)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                            | ~ r1_tmap_1(X3,X1,X4,X6) )
                          & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                            | r1_tmap_1(X3,X1,X4,X6) )
                          & X6 = X7
                          & m1_connsp_2(X5,X3,X6)
                          & r1_tarski(X5,u1_struct_0(X2))
                          & m1_subset_1(X7,u1_struct_0(X2)) )
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X7)
                          | ~ r1_tmap_1(sK3,X1,X4,X6) )
                        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X7)
                          | r1_tmap_1(sK3,X1,X4,X6) )
                        & X6 = X7
                        & m1_connsp_2(X5,sK3,X6)
                        & r1_tarski(X5,u1_struct_0(X2))
                        & m1_subset_1(X7,u1_struct_0(X2)) )
                    & m1_subset_1(X6,u1_struct_0(sK3)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) )
            & m1_pre_topc(X2,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                | ~ r1_tmap_1(X3,X1,X4,X6) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                | r1_tmap_1(X3,X1,X4,X6) )
                              & X6 = X7
                              & m1_connsp_2(X5,X3,X6)
                              & r1_tarski(X5,u1_struct_0(X2))
                              & m1_subset_1(X7,u1_struct_0(X2)) )
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
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
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ( ~ r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X7)
                              | ~ r1_tmap_1(X3,X1,X4,X6) )
                            & ( r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X7)
                              | r1_tmap_1(X3,X1,X4,X6) )
                            & X6 = X7
                            & m1_connsp_2(X5,X3,X6)
                            & r1_tarski(X5,u1_struct_0(sK2))
                            & m1_subset_1(X7,u1_struct_0(sK2)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                & m1_pre_topc(sK2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X1,X4,X6) )
                                  & X6 = X7
                                  & m1_connsp_2(X5,X3,X6)
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
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
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,sK1,X4,X6) )
                                & ( r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,sK1,X4,X6) )
                                & X6 = X7
                                & m1_connsp_2(X5,X3,X6)
                                & r1_tarski(X5,u1_struct_0(X2))
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | r1_tmap_1(X3,X1,X4,X6) )
                                    & X6 = X7
                                    & m1_connsp_2(X5,X3,X6)
                                    & r1_tarski(X5,u1_struct_0(X2))
                                    & m1_subset_1(X7,u1_struct_0(X2)) )
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
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
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X1,X4,X6) )
                                  & X6 = X7
                                  & m1_connsp_2(X5,X3,X6)
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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

fof(f36,plain,
    ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
      | ~ r1_tmap_1(sK3,sK1,sK4,sK6) )
    & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
      | r1_tmap_1(sK3,sK1,sK4,sK6) )
    & sK6 = sK7
    & m1_connsp_2(sK5,sK3,sK6)
    & r1_tarski(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK7,u1_struct_0(sK2))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f27,f35,f34,f33,f32,f31,f30,f29,f28])).

fof(f54,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X1,X0,X2,X5)
                                  | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                                & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | ~ r1_tmap_1(X1,X0,X2,X5) ) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | X5 != X6
      | ~ m1_connsp_2(X4,X1,X5)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f63,plain,(
    m1_connsp_2(sK5,sK3,sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f36])).

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
    inference(ennf_transformation,[],[f7])).

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

fof(f44,plain,(
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

fof(f69,plain,(
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
    inference(equality_resolution,[],[f44])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | X5 != X6
      | ~ m1_connsp_2(X4,X1,X5)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X6)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f62,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1307,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2009,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1307])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1309,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2007,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1309])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
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
    inference(cnf_transformation,[],[f41])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_644,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X4) != u1_struct_0(sK1)
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_18])).

cnf(c_645,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_649,plain,
    ( ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_645,c_19])).

cnf(c_650,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_649])).

cnf(c_1296,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X0_55,X2_55)
    | ~ m1_pre_topc(X1_55,X2_55)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X3_55))))
    | v2_struct_0(X2_55)
    | v2_struct_0(X3_55)
    | ~ l1_pre_topc(X2_55)
    | ~ l1_pre_topc(X3_55)
    | ~ v2_pre_topc(X2_55)
    | ~ v2_pre_topc(X3_55)
    | u1_struct_0(X1_55) != u1_struct_0(sK3)
    | u1_struct_0(X3_55) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X1_55),u1_struct_0(X3_55),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X2_55,X3_55,X1_55,X0_55,sK4) ),
    inference(subtyping,[status(esa)],[c_650])).

cnf(c_2020,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK4,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,sK4)
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1296])).

cnf(c_3218,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4)
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_pre_topc(X1_55,X2_55) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2020])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_33,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_34,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_35,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1325,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_2506,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_2584,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X0_55,X2_55)
    | ~ m1_pre_topc(X1_55,X2_55)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(sK1))))
    | v2_struct_0(X2_55)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X2_55)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X2_55)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X1_55) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X1_55),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X2_55,sK1,X1_55,X0_55,sK4) ),
    inference(instantiation,[status(thm)],[c_1296])).

cnf(c_2585,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4)
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(X1_55,X2_55) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2584])).

cnf(c_3424,plain,
    ( v2_pre_topc(X2_55) != iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(X1_55,X2_55) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4)
    | u1_struct_0(X0_55) != u1_struct_0(sK3)
    | l1_pre_topc(X2_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3218,c_33,c_34,c_35,c_2506,c_2585])).

cnf(c_3425,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4)
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_pre_topc(X1_55,X2_55) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_3424])).

cnf(c_3439,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_55) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3425])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1308,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2008,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1308])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_847,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_848,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(unflattening,[status(thm)],[c_847])).

cnf(c_1292,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54) ),
    inference(subtyping,[status(esa)],[c_848])).

cnf(c_2026,plain,
    ( k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1292])).

cnf(c_3027,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(superposition,[status(thm)],[c_2008,c_2026])).

cnf(c_3440,plain,
    ( k3_tmap_1(X0_55,sK1,sK3,X1_55,sK4) = k7_relat_1(sK4,u1_struct_0(X1_55))
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(X1_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_55) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3439,c_3027])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3445,plain,
    ( m1_pre_topc(sK3,X0_55) != iProver_top
    | m1_pre_topc(X1_55,sK3) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | k3_tmap_1(X0_55,sK1,sK3,X1_55,sK4) = k7_relat_1(sK4,u1_struct_0(X1_55))
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3440,c_42])).

cnf(c_3446,plain,
    ( k3_tmap_1(X0_55,sK1,sK3,X1_55,sK4) = k7_relat_1(sK4,u1_struct_0(X1_55))
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(X1_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_3445])).

cnf(c_3458,plain,
    ( k3_tmap_1(X0_55,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | m1_pre_topc(sK3,X0_55) != iProver_top
    | m1_pre_topc(sK2,X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_2007,c_3446])).

cnf(c_3541,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2009,c_3458])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_30,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_31,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_32,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_37,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3544,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3541,c_30,c_31,c_32,c_37])).

cnf(c_9,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1315,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2002,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1315])).

cnf(c_10,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1314,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2084,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2002,c_1314])).

cnf(c_3547,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3544,c_2084])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_695,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v1_funct_1(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_18])).

cnf(c_696,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_695])).

cnf(c_700,plain,
    ( ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X0,X1)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_696,c_19])).

cnf(c_701,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_700])).

cnf(c_1295,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X2_55))))
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X2_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X2_55)
    | u1_struct_0(X1_55) != u1_struct_0(sK3)
    | u1_struct_0(X2_55) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X1_55),u1_struct_0(X2_55),sK4,u1_struct_0(X0_55)) = k2_tmap_1(X1_55,X2_55,sK4,X0_55) ),
    inference(subtyping,[status(esa)],[c_701])).

cnf(c_2021,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK4,u1_struct_0(X2_55)) = k2_tmap_1(X0_55,X1_55,sK4,X2_55)
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1295])).

cnf(c_3200,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55)
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2021])).

cnf(c_2574,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(sK1))))
    | v2_struct_0(X1_55)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X1_55) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X1_55),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k2_tmap_1(X1_55,sK1,sK4,X0_55) ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_2580,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55)
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2574])).

cnf(c_3263,plain,
    ( v2_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55)
    | u1_struct_0(X0_55) != u1_struct_0(sK3)
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3200,c_33,c_34,c_35,c_2506,c_2580])).

cnf(c_3264,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55)
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_3263])).

cnf(c_3276,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k2_tmap_1(sK3,sK1,sK4,X0_55)
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3264])).

cnf(c_3277,plain,
    ( k2_tmap_1(sK3,sK1,sK4,X0_55) = k7_relat_1(sK4,u1_struct_0(X0_55))
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3276,c_3027])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_38,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_39,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1317,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2346,plain,
    ( ~ m1_pre_topc(X0_55,sK0)
    | l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1317])).

cnf(c_2347,plain,
    ( m1_pre_topc(X0_55,sK0) != iProver_top
    | l1_pre_topc(X0_55) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2346])).

cnf(c_2349,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2347])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1318,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v2_pre_topc(X1_55)
    | v2_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2360,plain,
    ( ~ m1_pre_topc(X0_55,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1318])).

cnf(c_2361,plain,
    ( m1_pre_topc(X0_55,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(X0_55) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2360])).

cnf(c_2363,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2361])).

cnf(c_3282,plain,
    ( k2_tmap_1(sK3,sK1,sK4,X0_55) = k7_relat_1(sK4,u1_struct_0(X0_55))
    | m1_pre_topc(X0_55,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3277,c_31,c_32,c_38,c_39,c_42,c_2349,c_2363])).

cnf(c_3290,plain,
    ( k2_tmap_1(sK3,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_2007,c_3282])).

cnf(c_5,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_11,negated_conjecture,
    ( m1_connsp_2(sK5,sK3,sK6) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_422,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | sK5 != X5
    | sK6 != X3
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_423,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
    | r1_tmap_1(sK3,X1,X2,sK6)
    | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X2) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_427,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
    | r1_tmap_1(sK3,X1,X2,sK6)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_423,c_21,c_15,c_14])).

cnf(c_428,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
    | r1_tmap_1(sK3,X1,X2,sK6)
    | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X2) ),
    inference(renaming,[status(thm)],[c_427])).

cnf(c_740,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
    | r1_tmap_1(sK3,X1,X2,sK6)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_428])).

cnf(c_741,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
    | r1_tmap_1(sK3,X1,sK4,sK6)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_740])).

cnf(c_745,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | r1_tmap_1(sK3,X1,sK4,sK6)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_741,c_19])).

cnf(c_746,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
    | r1_tmap_1(sK3,X1,sK4,sK6)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_745])).

cnf(c_1294,plain,
    ( ~ r1_tmap_1(X0_55,X1_55,k2_tmap_1(sK3,X1_55,sK4,X0_55),sK6)
    | r1_tmap_1(sK3,X1_55,sK4,sK6)
    | ~ r1_tarski(sK5,u1_struct_0(X0_55))
    | ~ m1_pre_topc(X0_55,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_55))))
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_746])).

cnf(c_1319,plain,
    ( ~ r1_tmap_1(X0_55,X1_55,k2_tmap_1(sK3,X1_55,sK4,X0_55),sK6)
    | r1_tmap_1(sK3,X1_55,sK4,sK6)
    | ~ r1_tarski(sK5,u1_struct_0(X0_55))
    | ~ m1_pre_topc(X0_55,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_55))))
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v2_pre_topc(X1_55)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1294])).

cnf(c_2023,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK1)
    | r1_tmap_1(X1_55,X0_55,k2_tmap_1(sK3,X0_55,sK4,X1_55),sK6) != iProver_top
    | r1_tmap_1(sK3,X0_55,sK4,sK6) = iProver_top
    | r1_tarski(sK5,u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X1_55,sK3) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_2124,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK1)
    | r1_tmap_1(X1_55,X0_55,k2_tmap_1(sK3,X0_55,sK4,X1_55),sK7) != iProver_top
    | r1_tmap_1(sK3,X0_55,sK4,sK7) = iProver_top
    | r1_tarski(sK5,u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X1_55,sK3) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2023,c_1314])).

cnf(c_1320,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1294])).

cnf(c_1378,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1320])).

cnf(c_2716,plain,
    ( v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X1_55,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X1_55)) != iProver_top
    | r1_tmap_1(sK3,X0_55,sK4,sK7) = iProver_top
    | r1_tmap_1(X1_55,X0_55,k2_tmap_1(sK3,X0_55,sK4,X1_55),sK7) != iProver_top
    | u1_struct_0(X0_55) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2124,c_31,c_32,c_39,c_1378,c_2349,c_2363])).

cnf(c_2717,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK1)
    | r1_tmap_1(X1_55,X0_55,k2_tmap_1(sK3,X0_55,sK4,X1_55),sK7) != iProver_top
    | r1_tmap_1(sK3,X0_55,sK4,sK7) = iProver_top
    | r1_tarski(sK5,u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X1_55,sK3) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_2716])).

cnf(c_2733,plain,
    ( r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | r1_tarski(sK5,u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2717])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_36,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_43,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_46,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1311,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2005,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1311])).

cnf(c_2055,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2005,c_1314])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1316,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2001,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1316])).

cnf(c_2089,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2001,c_1314])).

cnf(c_2496,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_7,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_578,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v1_funct_1(X2)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_579,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_583,plain,
    ( ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_579,c_19])).

cnf(c_584,plain,
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
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_583])).

cnf(c_1297,plain,
    ( r1_tmap_1(X0_55,X1_55,k3_tmap_1(X2_55,X1_55,X3_55,X0_55,sK4),X0_53)
    | ~ r1_tmap_1(X3_55,X1_55,sK4,X0_53)
    | ~ m1_pre_topc(X0_55,X2_55)
    | ~ m1_pre_topc(X3_55,X2_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_55))
    | ~ m1_subset_1(X0_53,u1_struct_0(X3_55))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_55),u1_struct_0(X1_55))))
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | v2_struct_0(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X2_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X2_55)
    | u1_struct_0(X3_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_584])).

cnf(c_2331,plain,
    ( r1_tmap_1(X0_55,sK1,k3_tmap_1(X1_55,sK1,X2_55,X0_55,sK4),X0_53)
    | ~ r1_tmap_1(X2_55,sK1,sK4,X0_53)
    | ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X0_55,X2_55)
    | ~ m1_pre_topc(X2_55,X1_55)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_55))
    | ~ m1_subset_1(X0_53,u1_struct_0(X2_55))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(sK1))))
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X2_55) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_2599,plain,
    ( ~ r1_tmap_1(X0_55,sK1,sK4,X0_53)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X0_55,sK2,sK4),X0_53)
    | ~ m1_pre_topc(X0_55,sK0)
    | ~ m1_pre_topc(sK2,X0_55)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_55))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1))))
    | v2_struct_0(X0_55)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2331])).

cnf(c_2991,plain,
    ( ~ r1_tmap_1(X0_55,sK1,sK4,sK7)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X0_55,sK2,sK4),sK7)
    | ~ m1_pre_topc(X0_55,sK0)
    | ~ m1_pre_topc(sK2,X0_55)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK7,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1))))
    | v2_struct_0(X0_55)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2599])).

cnf(c_2992,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tmap_1(X0_55,sK1,sK4,sK7) != iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X0_55,sK2,sK4),sK7) = iProver_top
    | m1_pre_topc(X0_55,sK0) != iProver_top
    | m1_pre_topc(sK2,X0_55) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2991])).

cnf(c_2994,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2992])).

cnf(c_3122,plain,
    ( v2_struct_0(X0_55) = iProver_top
    | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2733,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_42,c_43,c_46,c_2055,c_2089,c_2496,c_2506,c_2994])).

cnf(c_3123,plain,
    ( r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | v2_struct_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_3122])).

cnf(c_3357,plain,
    ( r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),sK7) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3290,c_3123])).

cnf(c_6,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_368,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | sK5 != X5
    | sK6 != X3
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_369,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
    | ~ r1_tmap_1(sK3,X1,X2,sK6)
    | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X2) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_373,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ r1_tmap_1(sK3,X1,X2,sK6)
    | r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_21,c_15,c_14])).

cnf(c_374,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
    | ~ r1_tmap_1(sK3,X1,X2,sK6)
    | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X2) ),
    inference(renaming,[status(thm)],[c_373])).

cnf(c_791,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
    | ~ r1_tmap_1(sK3,X1,X2,sK6)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_374])).

cnf(c_792,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
    | ~ r1_tmap_1(sK3,X1,sK4,sK6)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_791])).

cnf(c_796,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ r1_tmap_1(sK3,X1,sK4,sK6)
    | r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_792,c_19])).

cnf(c_797,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
    | ~ r1_tmap_1(sK3,X1,sK4,sK6)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_796])).

cnf(c_1293,plain,
    ( r1_tmap_1(X0_55,X1_55,k2_tmap_1(sK3,X1_55,sK4,X0_55),sK6)
    | ~ r1_tmap_1(sK3,X1_55,sK4,sK6)
    | ~ r1_tarski(sK5,u1_struct_0(X0_55))
    | ~ m1_pre_topc(X0_55,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_55))))
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_797])).

cnf(c_1321,plain,
    ( r1_tmap_1(X0_55,X1_55,k2_tmap_1(sK3,X1_55,sK4,X0_55),sK6)
    | ~ r1_tmap_1(sK3,X1_55,sK4,sK6)
    | ~ r1_tarski(sK5,u1_struct_0(X0_55))
    | ~ m1_pre_topc(X0_55,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_55))))
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v2_pre_topc(X1_55)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1293])).

cnf(c_2025,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK1)
    | r1_tmap_1(X1_55,X0_55,k2_tmap_1(sK3,X0_55,sK4,X1_55),sK6) = iProver_top
    | r1_tmap_1(sK3,X0_55,sK4,sK6) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X1_55,sK3) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1321])).

cnf(c_2149,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK1)
    | r1_tmap_1(X1_55,X0_55,k2_tmap_1(sK3,X0_55,sK4,X1_55),sK7) = iProver_top
    | r1_tmap_1(sK3,X0_55,sK4,sK7) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X1_55,sK3) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2025,c_1314])).

cnf(c_1322,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1293])).

cnf(c_1382,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1322])).

cnf(c_2811,plain,
    ( v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X1_55,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X1_55)) != iProver_top
    | r1_tmap_1(sK3,X0_55,sK4,sK7) != iProver_top
    | r1_tmap_1(X1_55,X0_55,k2_tmap_1(sK3,X0_55,sK4,X1_55),sK7) = iProver_top
    | u1_struct_0(X0_55) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2149,c_31,c_32,c_39,c_1382,c_2349,c_2363])).

cnf(c_2812,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK1)
    | r1_tmap_1(X1_55,X0_55,k2_tmap_1(sK3,X0_55,sK4,X1_55),sK7) = iProver_top
    | r1_tmap_1(sK3,X0_55,sK4,sK7) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X1_55,sK3) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_2811])).

cnf(c_2828,plain,
    ( r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2812])).

cnf(c_3134,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2828,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_42,c_43,c_46,c_2055,c_2089,c_2496,c_2506,c_2994])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_47,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3547,c_3357,c_3134,c_47,c_46,c_43,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:37:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.20/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.01  
% 2.20/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.20/1.01  
% 2.20/1.01  ------  iProver source info
% 2.20/1.01  
% 2.20/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.20/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.20/1.01  git: non_committed_changes: false
% 2.20/1.01  git: last_make_outside_of_git: false
% 2.20/1.01  
% 2.20/1.01  ------ 
% 2.20/1.01  
% 2.20/1.01  ------ Input Options
% 2.20/1.01  
% 2.20/1.01  --out_options                           all
% 2.20/1.01  --tptp_safe_out                         true
% 2.20/1.01  --problem_path                          ""
% 2.20/1.01  --include_path                          ""
% 2.20/1.01  --clausifier                            res/vclausify_rel
% 2.20/1.01  --clausifier_options                    --mode clausify
% 2.20/1.01  --stdin                                 false
% 2.20/1.01  --stats_out                             all
% 2.20/1.01  
% 2.20/1.01  ------ General Options
% 2.20/1.01  
% 2.20/1.01  --fof                                   false
% 2.20/1.01  --time_out_real                         305.
% 2.20/1.01  --time_out_virtual                      -1.
% 2.20/1.01  --symbol_type_check                     false
% 2.20/1.01  --clausify_out                          false
% 2.20/1.01  --sig_cnt_out                           false
% 2.20/1.01  --trig_cnt_out                          false
% 2.20/1.01  --trig_cnt_out_tolerance                1.
% 2.20/1.01  --trig_cnt_out_sk_spl                   false
% 2.20/1.01  --abstr_cl_out                          false
% 2.20/1.01  
% 2.20/1.01  ------ Global Options
% 2.20/1.01  
% 2.20/1.01  --schedule                              default
% 2.20/1.01  --add_important_lit                     false
% 2.20/1.01  --prop_solver_per_cl                    1000
% 2.20/1.01  --min_unsat_core                        false
% 2.20/1.01  --soft_assumptions                      false
% 2.20/1.01  --soft_lemma_size                       3
% 2.20/1.01  --prop_impl_unit_size                   0
% 2.20/1.01  --prop_impl_unit                        []
% 2.20/1.01  --share_sel_clauses                     true
% 2.20/1.01  --reset_solvers                         false
% 2.20/1.01  --bc_imp_inh                            [conj_cone]
% 2.20/1.01  --conj_cone_tolerance                   3.
% 2.20/1.01  --extra_neg_conj                        none
% 2.20/1.01  --large_theory_mode                     true
% 2.20/1.01  --prolific_symb_bound                   200
% 2.20/1.01  --lt_threshold                          2000
% 2.20/1.01  --clause_weak_htbl                      true
% 2.20/1.01  --gc_record_bc_elim                     false
% 2.20/1.01  
% 2.20/1.01  ------ Preprocessing Options
% 2.20/1.01  
% 2.20/1.01  --preprocessing_flag                    true
% 2.20/1.01  --time_out_prep_mult                    0.1
% 2.20/1.01  --splitting_mode                        input
% 2.20/1.01  --splitting_grd                         true
% 2.20/1.01  --splitting_cvd                         false
% 2.20/1.01  --splitting_cvd_svl                     false
% 2.20/1.01  --splitting_nvd                         32
% 2.20/1.01  --sub_typing                            true
% 2.20/1.01  --prep_gs_sim                           true
% 2.20/1.01  --prep_unflatten                        true
% 2.20/1.01  --prep_res_sim                          true
% 2.20/1.01  --prep_upred                            true
% 2.20/1.01  --prep_sem_filter                       exhaustive
% 2.20/1.01  --prep_sem_filter_out                   false
% 2.20/1.01  --pred_elim                             true
% 2.20/1.01  --res_sim_input                         true
% 2.20/1.01  --eq_ax_congr_red                       true
% 2.20/1.01  --pure_diseq_elim                       true
% 2.20/1.01  --brand_transform                       false
% 2.20/1.01  --non_eq_to_eq                          false
% 2.20/1.01  --prep_def_merge                        true
% 2.20/1.01  --prep_def_merge_prop_impl              false
% 2.20/1.01  --prep_def_merge_mbd                    true
% 2.20/1.01  --prep_def_merge_tr_red                 false
% 2.20/1.01  --prep_def_merge_tr_cl                  false
% 2.20/1.01  --smt_preprocessing                     true
% 2.20/1.01  --smt_ac_axioms                         fast
% 2.20/1.01  --preprocessed_out                      false
% 2.20/1.01  --preprocessed_stats                    false
% 2.20/1.01  
% 2.20/1.01  ------ Abstraction refinement Options
% 2.20/1.01  
% 2.20/1.01  --abstr_ref                             []
% 2.20/1.01  --abstr_ref_prep                        false
% 2.20/1.01  --abstr_ref_until_sat                   false
% 2.20/1.01  --abstr_ref_sig_restrict                funpre
% 2.20/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.20/1.01  --abstr_ref_under                       []
% 2.20/1.01  
% 2.20/1.01  ------ SAT Options
% 2.20/1.01  
% 2.20/1.01  --sat_mode                              false
% 2.20/1.01  --sat_fm_restart_options                ""
% 2.20/1.01  --sat_gr_def                            false
% 2.20/1.01  --sat_epr_types                         true
% 2.20/1.01  --sat_non_cyclic_types                  false
% 2.20/1.01  --sat_finite_models                     false
% 2.20/1.01  --sat_fm_lemmas                         false
% 2.20/1.01  --sat_fm_prep                           false
% 2.20/1.01  --sat_fm_uc_incr                        true
% 2.20/1.01  --sat_out_model                         small
% 2.20/1.01  --sat_out_clauses                       false
% 2.20/1.01  
% 2.20/1.01  ------ QBF Options
% 2.20/1.01  
% 2.20/1.01  --qbf_mode                              false
% 2.20/1.01  --qbf_elim_univ                         false
% 2.20/1.01  --qbf_dom_inst                          none
% 2.20/1.01  --qbf_dom_pre_inst                      false
% 2.20/1.01  --qbf_sk_in                             false
% 2.20/1.01  --qbf_pred_elim                         true
% 2.20/1.01  --qbf_split                             512
% 2.20/1.01  
% 2.20/1.01  ------ BMC1 Options
% 2.20/1.01  
% 2.20/1.01  --bmc1_incremental                      false
% 2.20/1.01  --bmc1_axioms                           reachable_all
% 2.20/1.01  --bmc1_min_bound                        0
% 2.20/1.01  --bmc1_max_bound                        -1
% 2.20/1.01  --bmc1_max_bound_default                -1
% 2.20/1.01  --bmc1_symbol_reachability              true
% 2.20/1.01  --bmc1_property_lemmas                  false
% 2.20/1.01  --bmc1_k_induction                      false
% 2.20/1.01  --bmc1_non_equiv_states                 false
% 2.20/1.01  --bmc1_deadlock                         false
% 2.20/1.01  --bmc1_ucm                              false
% 2.20/1.01  --bmc1_add_unsat_core                   none
% 2.20/1.01  --bmc1_unsat_core_children              false
% 2.20/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.20/1.01  --bmc1_out_stat                         full
% 2.20/1.01  --bmc1_ground_init                      false
% 2.20/1.01  --bmc1_pre_inst_next_state              false
% 2.20/1.01  --bmc1_pre_inst_state                   false
% 2.20/1.01  --bmc1_pre_inst_reach_state             false
% 2.20/1.01  --bmc1_out_unsat_core                   false
% 2.20/1.01  --bmc1_aig_witness_out                  false
% 2.20/1.01  --bmc1_verbose                          false
% 2.20/1.01  --bmc1_dump_clauses_tptp                false
% 2.20/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.20/1.01  --bmc1_dump_file                        -
% 2.20/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.20/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.20/1.01  --bmc1_ucm_extend_mode                  1
% 2.20/1.01  --bmc1_ucm_init_mode                    2
% 2.20/1.01  --bmc1_ucm_cone_mode                    none
% 2.20/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.20/1.01  --bmc1_ucm_relax_model                  4
% 2.20/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.20/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.20/1.01  --bmc1_ucm_layered_model                none
% 2.20/1.01  --bmc1_ucm_max_lemma_size               10
% 2.20/1.01  
% 2.20/1.01  ------ AIG Options
% 2.20/1.01  
% 2.20/1.01  --aig_mode                              false
% 2.20/1.01  
% 2.20/1.01  ------ Instantiation Options
% 2.20/1.01  
% 2.20/1.01  --instantiation_flag                    true
% 2.20/1.01  --inst_sos_flag                         false
% 2.20/1.01  --inst_sos_phase                        true
% 2.20/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.20/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.20/1.01  --inst_lit_sel_side                     num_symb
% 2.20/1.01  --inst_solver_per_active                1400
% 2.20/1.01  --inst_solver_calls_frac                1.
% 2.20/1.01  --inst_passive_queue_type               priority_queues
% 2.20/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.20/1.01  --inst_passive_queues_freq              [25;2]
% 2.20/1.01  --inst_dismatching                      true
% 2.20/1.01  --inst_eager_unprocessed_to_passive     true
% 2.20/1.01  --inst_prop_sim_given                   true
% 2.20/1.01  --inst_prop_sim_new                     false
% 2.20/1.01  --inst_subs_new                         false
% 2.20/1.01  --inst_eq_res_simp                      false
% 2.20/1.01  --inst_subs_given                       false
% 2.20/1.01  --inst_orphan_elimination               true
% 2.20/1.01  --inst_learning_loop_flag               true
% 2.20/1.01  --inst_learning_start                   3000
% 2.20/1.01  --inst_learning_factor                  2
% 2.20/1.01  --inst_start_prop_sim_after_learn       3
% 2.20/1.01  --inst_sel_renew                        solver
% 2.20/1.01  --inst_lit_activity_flag                true
% 2.20/1.01  --inst_restr_to_given                   false
% 2.20/1.01  --inst_activity_threshold               500
% 2.20/1.01  --inst_out_proof                        true
% 2.20/1.01  
% 2.20/1.01  ------ Resolution Options
% 2.20/1.01  
% 2.20/1.01  --resolution_flag                       true
% 2.20/1.01  --res_lit_sel                           adaptive
% 2.20/1.01  --res_lit_sel_side                      none
% 2.20/1.01  --res_ordering                          kbo
% 2.20/1.01  --res_to_prop_solver                    active
% 2.20/1.01  --res_prop_simpl_new                    false
% 2.20/1.01  --res_prop_simpl_given                  true
% 2.20/1.01  --res_passive_queue_type                priority_queues
% 2.20/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.20/1.01  --res_passive_queues_freq               [15;5]
% 2.20/1.01  --res_forward_subs                      full
% 2.20/1.01  --res_backward_subs                     full
% 2.20/1.01  --res_forward_subs_resolution           true
% 2.20/1.01  --res_backward_subs_resolution          true
% 2.20/1.01  --res_orphan_elimination                true
% 2.20/1.01  --res_time_limit                        2.
% 2.20/1.01  --res_out_proof                         true
% 2.20/1.01  
% 2.20/1.01  ------ Superposition Options
% 2.20/1.01  
% 2.20/1.01  --superposition_flag                    true
% 2.20/1.01  --sup_passive_queue_type                priority_queues
% 2.20/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.20/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.20/1.01  --demod_completeness_check              fast
% 2.20/1.01  --demod_use_ground                      true
% 2.20/1.01  --sup_to_prop_solver                    passive
% 2.20/1.01  --sup_prop_simpl_new                    true
% 2.20/1.01  --sup_prop_simpl_given                  true
% 2.20/1.01  --sup_fun_splitting                     false
% 2.20/1.01  --sup_smt_interval                      50000
% 2.20/1.01  
% 2.20/1.01  ------ Superposition Simplification Setup
% 2.20/1.01  
% 2.20/1.01  --sup_indices_passive                   []
% 2.20/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.20/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.01  --sup_full_bw                           [BwDemod]
% 2.20/1.01  --sup_immed_triv                        [TrivRules]
% 2.20/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.20/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.01  --sup_immed_bw_main                     []
% 2.20/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.20/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/1.01  
% 2.20/1.01  ------ Combination Options
% 2.20/1.01  
% 2.20/1.01  --comb_res_mult                         3
% 2.20/1.01  --comb_sup_mult                         2
% 2.20/1.01  --comb_inst_mult                        10
% 2.20/1.01  
% 2.20/1.01  ------ Debug Options
% 2.20/1.01  
% 2.20/1.01  --dbg_backtrace                         false
% 2.20/1.01  --dbg_dump_prop_clauses                 false
% 2.20/1.01  --dbg_dump_prop_clauses_file            -
% 2.20/1.01  --dbg_out_stat                          false
% 2.20/1.01  ------ Parsing...
% 2.20/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.20/1.01  
% 2.20/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.20/1.01  
% 2.20/1.01  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.20/1.01  
% 2.20/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.20/1.01  ------ Proving...
% 2.20/1.01  ------ Problem Properties 
% 2.20/1.01  
% 2.20/1.01  
% 2.20/1.01  clauses                                 29
% 2.20/1.01  conjectures                             19
% 2.20/1.01  EPR                                     16
% 2.20/1.01  Horn                                    23
% 2.20/1.01  unary                                   17
% 2.20/1.01  binary                                  3
% 2.20/1.01  lits                                    102
% 2.20/1.01  lits eq                                 12
% 2.20/1.01  fd_pure                                 0
% 2.20/1.01  fd_pseudo                               0
% 2.20/1.01  fd_cond                                 0
% 2.20/1.01  fd_pseudo_cond                          0
% 2.20/1.01  AC symbols                              0
% 2.20/1.01  
% 2.20/1.01  ------ Schedule dynamic 5 is on 
% 2.20/1.01  
% 2.20/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.20/1.01  
% 2.20/1.01  
% 2.20/1.01  ------ 
% 2.20/1.01  Current options:
% 2.20/1.01  ------ 
% 2.20/1.01  
% 2.20/1.01  ------ Input Options
% 2.20/1.01  
% 2.20/1.01  --out_options                           all
% 2.20/1.01  --tptp_safe_out                         true
% 2.20/1.01  --problem_path                          ""
% 2.20/1.01  --include_path                          ""
% 2.20/1.01  --clausifier                            res/vclausify_rel
% 2.20/1.01  --clausifier_options                    --mode clausify
% 2.20/1.01  --stdin                                 false
% 2.20/1.01  --stats_out                             all
% 2.20/1.01  
% 2.20/1.01  ------ General Options
% 2.20/1.01  
% 2.20/1.01  --fof                                   false
% 2.20/1.01  --time_out_real                         305.
% 2.20/1.01  --time_out_virtual                      -1.
% 2.20/1.01  --symbol_type_check                     false
% 2.20/1.01  --clausify_out                          false
% 2.20/1.01  --sig_cnt_out                           false
% 2.20/1.01  --trig_cnt_out                          false
% 2.20/1.01  --trig_cnt_out_tolerance                1.
% 2.20/1.01  --trig_cnt_out_sk_spl                   false
% 2.20/1.01  --abstr_cl_out                          false
% 2.20/1.01  
% 2.20/1.01  ------ Global Options
% 2.20/1.01  
% 2.20/1.01  --schedule                              default
% 2.20/1.01  --add_important_lit                     false
% 2.20/1.01  --prop_solver_per_cl                    1000
% 2.20/1.01  --min_unsat_core                        false
% 2.20/1.01  --soft_assumptions                      false
% 2.20/1.01  --soft_lemma_size                       3
% 2.20/1.01  --prop_impl_unit_size                   0
% 2.20/1.01  --prop_impl_unit                        []
% 2.20/1.01  --share_sel_clauses                     true
% 2.20/1.01  --reset_solvers                         false
% 2.20/1.01  --bc_imp_inh                            [conj_cone]
% 2.20/1.01  --conj_cone_tolerance                   3.
% 2.20/1.01  --extra_neg_conj                        none
% 2.20/1.01  --large_theory_mode                     true
% 2.20/1.01  --prolific_symb_bound                   200
% 2.20/1.01  --lt_threshold                          2000
% 2.20/1.01  --clause_weak_htbl                      true
% 2.20/1.01  --gc_record_bc_elim                     false
% 2.20/1.01  
% 2.20/1.01  ------ Preprocessing Options
% 2.20/1.01  
% 2.20/1.01  --preprocessing_flag                    true
% 2.20/1.01  --time_out_prep_mult                    0.1
% 2.20/1.01  --splitting_mode                        input
% 2.20/1.01  --splitting_grd                         true
% 2.20/1.01  --splitting_cvd                         false
% 2.20/1.01  --splitting_cvd_svl                     false
% 2.20/1.01  --splitting_nvd                         32
% 2.20/1.01  --sub_typing                            true
% 2.20/1.01  --prep_gs_sim                           true
% 2.20/1.01  --prep_unflatten                        true
% 2.20/1.01  --prep_res_sim                          true
% 2.20/1.01  --prep_upred                            true
% 2.20/1.01  --prep_sem_filter                       exhaustive
% 2.20/1.01  --prep_sem_filter_out                   false
% 2.20/1.01  --pred_elim                             true
% 2.20/1.01  --res_sim_input                         true
% 2.20/1.01  --eq_ax_congr_red                       true
% 2.20/1.01  --pure_diseq_elim                       true
% 2.20/1.01  --brand_transform                       false
% 2.20/1.01  --non_eq_to_eq                          false
% 2.20/1.01  --prep_def_merge                        true
% 2.20/1.01  --prep_def_merge_prop_impl              false
% 2.20/1.01  --prep_def_merge_mbd                    true
% 2.20/1.01  --prep_def_merge_tr_red                 false
% 2.20/1.01  --prep_def_merge_tr_cl                  false
% 2.20/1.01  --smt_preprocessing                     true
% 2.20/1.01  --smt_ac_axioms                         fast
% 2.20/1.01  --preprocessed_out                      false
% 2.20/1.01  --preprocessed_stats                    false
% 2.20/1.01  
% 2.20/1.01  ------ Abstraction refinement Options
% 2.20/1.01  
% 2.20/1.01  --abstr_ref                             []
% 2.20/1.01  --abstr_ref_prep                        false
% 2.20/1.01  --abstr_ref_until_sat                   false
% 2.20/1.01  --abstr_ref_sig_restrict                funpre
% 2.20/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.20/1.01  --abstr_ref_under                       []
% 2.20/1.01  
% 2.20/1.01  ------ SAT Options
% 2.20/1.01  
% 2.20/1.01  --sat_mode                              false
% 2.20/1.01  --sat_fm_restart_options                ""
% 2.20/1.01  --sat_gr_def                            false
% 2.20/1.01  --sat_epr_types                         true
% 2.20/1.01  --sat_non_cyclic_types                  false
% 2.20/1.01  --sat_finite_models                     false
% 2.20/1.01  --sat_fm_lemmas                         false
% 2.20/1.01  --sat_fm_prep                           false
% 2.20/1.01  --sat_fm_uc_incr                        true
% 2.20/1.01  --sat_out_model                         small
% 2.20/1.01  --sat_out_clauses                       false
% 2.20/1.01  
% 2.20/1.01  ------ QBF Options
% 2.20/1.01  
% 2.20/1.01  --qbf_mode                              false
% 2.20/1.01  --qbf_elim_univ                         false
% 2.20/1.01  --qbf_dom_inst                          none
% 2.20/1.01  --qbf_dom_pre_inst                      false
% 2.20/1.01  --qbf_sk_in                             false
% 2.20/1.01  --qbf_pred_elim                         true
% 2.20/1.01  --qbf_split                             512
% 2.20/1.01  
% 2.20/1.01  ------ BMC1 Options
% 2.20/1.01  
% 2.20/1.01  --bmc1_incremental                      false
% 2.20/1.01  --bmc1_axioms                           reachable_all
% 2.20/1.01  --bmc1_min_bound                        0
% 2.20/1.01  --bmc1_max_bound                        -1
% 2.20/1.01  --bmc1_max_bound_default                -1
% 2.20/1.01  --bmc1_symbol_reachability              true
% 2.20/1.01  --bmc1_property_lemmas                  false
% 2.20/1.01  --bmc1_k_induction                      false
% 2.20/1.01  --bmc1_non_equiv_states                 false
% 2.20/1.01  --bmc1_deadlock                         false
% 2.20/1.01  --bmc1_ucm                              false
% 2.20/1.01  --bmc1_add_unsat_core                   none
% 2.20/1.01  --bmc1_unsat_core_children              false
% 2.20/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.20/1.01  --bmc1_out_stat                         full
% 2.20/1.01  --bmc1_ground_init                      false
% 2.20/1.01  --bmc1_pre_inst_next_state              false
% 2.20/1.01  --bmc1_pre_inst_state                   false
% 2.20/1.01  --bmc1_pre_inst_reach_state             false
% 2.20/1.01  --bmc1_out_unsat_core                   false
% 2.20/1.01  --bmc1_aig_witness_out                  false
% 2.20/1.01  --bmc1_verbose                          false
% 2.20/1.01  --bmc1_dump_clauses_tptp                false
% 2.20/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.20/1.01  --bmc1_dump_file                        -
% 2.20/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.20/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.20/1.01  --bmc1_ucm_extend_mode                  1
% 2.20/1.01  --bmc1_ucm_init_mode                    2
% 2.20/1.01  --bmc1_ucm_cone_mode                    none
% 2.20/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.20/1.01  --bmc1_ucm_relax_model                  4
% 2.20/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.20/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.20/1.01  --bmc1_ucm_layered_model                none
% 2.20/1.01  --bmc1_ucm_max_lemma_size               10
% 2.20/1.01  
% 2.20/1.01  ------ AIG Options
% 2.20/1.01  
% 2.20/1.01  --aig_mode                              false
% 2.20/1.01  
% 2.20/1.01  ------ Instantiation Options
% 2.20/1.01  
% 2.20/1.01  --instantiation_flag                    true
% 2.20/1.01  --inst_sos_flag                         false
% 2.20/1.01  --inst_sos_phase                        true
% 2.20/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.20/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.20/1.01  --inst_lit_sel_side                     none
% 2.20/1.01  --inst_solver_per_active                1400
% 2.20/1.01  --inst_solver_calls_frac                1.
% 2.20/1.01  --inst_passive_queue_type               priority_queues
% 2.20/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.20/1.01  --inst_passive_queues_freq              [25;2]
% 2.20/1.01  --inst_dismatching                      true
% 2.20/1.01  --inst_eager_unprocessed_to_passive     true
% 2.20/1.01  --inst_prop_sim_given                   true
% 2.20/1.01  --inst_prop_sim_new                     false
% 2.20/1.01  --inst_subs_new                         false
% 2.20/1.01  --inst_eq_res_simp                      false
% 2.20/1.01  --inst_subs_given                       false
% 2.20/1.01  --inst_orphan_elimination               true
% 2.20/1.01  --inst_learning_loop_flag               true
% 2.20/1.01  --inst_learning_start                   3000
% 2.20/1.01  --inst_learning_factor                  2
% 2.20/1.01  --inst_start_prop_sim_after_learn       3
% 2.20/1.01  --inst_sel_renew                        solver
% 2.20/1.01  --inst_lit_activity_flag                true
% 2.20/1.01  --inst_restr_to_given                   false
% 2.20/1.01  --inst_activity_threshold               500
% 2.20/1.01  --inst_out_proof                        true
% 2.20/1.01  
% 2.20/1.01  ------ Resolution Options
% 2.20/1.01  
% 2.20/1.01  --resolution_flag                       false
% 2.20/1.01  --res_lit_sel                           adaptive
% 2.20/1.01  --res_lit_sel_side                      none
% 2.20/1.01  --res_ordering                          kbo
% 2.20/1.01  --res_to_prop_solver                    active
% 2.20/1.01  --res_prop_simpl_new                    false
% 2.20/1.01  --res_prop_simpl_given                  true
% 2.20/1.01  --res_passive_queue_type                priority_queues
% 2.20/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.20/1.01  --res_passive_queues_freq               [15;5]
% 2.20/1.01  --res_forward_subs                      full
% 2.20/1.01  --res_backward_subs                     full
% 2.20/1.01  --res_forward_subs_resolution           true
% 2.20/1.01  --res_backward_subs_resolution          true
% 2.20/1.01  --res_orphan_elimination                true
% 2.20/1.01  --res_time_limit                        2.
% 2.20/1.01  --res_out_proof                         true
% 2.20/1.01  
% 2.20/1.01  ------ Superposition Options
% 2.20/1.01  
% 2.20/1.01  --superposition_flag                    true
% 2.20/1.01  --sup_passive_queue_type                priority_queues
% 2.20/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.20/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.20/1.01  --demod_completeness_check              fast
% 2.20/1.01  --demod_use_ground                      true
% 2.20/1.01  --sup_to_prop_solver                    passive
% 2.20/1.01  --sup_prop_simpl_new                    true
% 2.20/1.01  --sup_prop_simpl_given                  true
% 2.20/1.01  --sup_fun_splitting                     false
% 2.20/1.01  --sup_smt_interval                      50000
% 2.20/1.01  
% 2.20/1.01  ------ Superposition Simplification Setup
% 2.20/1.01  
% 2.20/1.01  --sup_indices_passive                   []
% 2.20/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.20/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.01  --sup_full_bw                           [BwDemod]
% 2.20/1.01  --sup_immed_triv                        [TrivRules]
% 2.20/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.20/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.01  --sup_immed_bw_main                     []
% 2.20/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.20/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/1.01  
% 2.20/1.01  ------ Combination Options
% 2.20/1.01  
% 2.20/1.01  --comb_res_mult                         3
% 2.20/1.01  --comb_sup_mult                         2
% 2.20/1.01  --comb_inst_mult                        10
% 2.20/1.01  
% 2.20/1.01  ------ Debug Options
% 2.20/1.01  
% 2.20/1.01  --dbg_backtrace                         false
% 2.20/1.01  --dbg_dump_prop_clauses                 false
% 2.20/1.01  --dbg_dump_prop_clauses_file            -
% 2.20/1.01  --dbg_out_stat                          false
% 2.20/1.01  
% 2.20/1.01  
% 2.20/1.01  
% 2.20/1.01  
% 2.20/1.01  ------ Proving...
% 2.20/1.01  
% 2.20/1.01  
% 2.20/1.01  % SZS status Theorem for theBenchmark.p
% 2.20/1.01  
% 2.20/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.20/1.01  
% 2.20/1.01  fof(f8,conjecture,(
% 2.20/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.20/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.01  
% 2.20/1.01  fof(f9,negated_conjecture,(
% 2.20/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.20/1.01    inference(negated_conjecture,[],[f8])).
% 2.20/1.01  
% 2.20/1.01  fof(f23,plain,(
% 2.20/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.20/1.01    inference(ennf_transformation,[],[f9])).
% 2.20/1.01  
% 2.20/1.01  fof(f24,plain,(
% 2.20/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.20/1.01    inference(flattening,[],[f23])).
% 2.20/1.01  
% 2.20/1.01  fof(f26,plain,(
% 2.20/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6))) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.20/1.01    inference(nnf_transformation,[],[f24])).
% 2.20/1.01  
% 2.20/1.01  fof(f27,plain,(
% 2.20/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.20/1.01    inference(flattening,[],[f26])).
% 2.20/1.01  
% 2.20/1.01  fof(f35,plain,(
% 2.20/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) | r1_tmap_1(X3,X1,X4,X6)) & sK7 = X6 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 2.20/1.01    introduced(choice_axiom,[])).
% 2.20/1.01  
% 2.20/1.01  fof(f34,plain,(
% 2.20/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,sK6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,sK6)) & sK6 = X7 & m1_connsp_2(X5,X3,sK6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.20/1.01    introduced(choice_axiom,[])).
% 2.20/1.01  
% 2.20/1.01  fof(f33,plain,(
% 2.20/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & m1_connsp_2(sK5,X3,X6) & r1_tarski(sK5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))))) )),
% 2.20/1.01    introduced(choice_axiom,[])).
% 2.20/1.01  
% 2.20/1.01  fof(f32,plain,(
% 2.20/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X7) | ~r1_tmap_1(X3,X1,sK4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X7) | r1_tmap_1(X3,X1,sK4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.20/1.01    introduced(choice_axiom,[])).
% 2.20/1.01  
% 2.20/1.01  fof(f31,plain,(
% 2.20/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X7) | ~r1_tmap_1(sK3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X7) | r1_tmap_1(sK3,X1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,sK3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.20/1.01    introduced(choice_axiom,[])).
% 2.20/1.01  
% 2.20/1.01  fof(f30,plain,(
% 2.20/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.20/1.01    introduced(choice_axiom,[])).
% 2.20/1.01  
% 2.20/1.01  fof(f29,plain,(
% 2.20/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.20/1.01    introduced(choice_axiom,[])).
% 2.20/1.01  
% 2.20/1.01  fof(f28,plain,(
% 2.20/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.20/1.01    introduced(choice_axiom,[])).
% 2.20/1.01  
% 2.20/1.01  fof(f36,plain,(
% 2.20/1.01    ((((((((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)) & sK6 = sK7 & m1_connsp_2(sK5,sK3,sK6) & r1_tarski(sK5,u1_struct_0(sK2)) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.20/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f27,f35,f34,f33,f32,f31,f30,f29,f28])).
% 2.20/1.01  
% 2.20/1.01  fof(f54,plain,(
% 2.20/1.01    m1_pre_topc(sK3,sK0)),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f58,plain,(
% 2.20/1.01    m1_pre_topc(sK2,sK3)),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f5,axiom,(
% 2.20/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.20/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.01  
% 2.20/1.01  fof(f17,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.20/1.01    inference(ennf_transformation,[],[f5])).
% 2.20/1.01  
% 2.20/1.01  fof(f18,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/1.01    inference(flattening,[],[f17])).
% 2.20/1.01  
% 2.20/1.01  fof(f41,plain,(
% 2.20/1.01    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/1.01    inference(cnf_transformation,[],[f18])).
% 2.20/1.01  
% 2.20/1.01  fof(f56,plain,(
% 2.20/1.01    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f55,plain,(
% 2.20/1.01    v1_funct_1(sK4)),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f48,plain,(
% 2.20/1.01    ~v2_struct_0(sK1)),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f49,plain,(
% 2.20/1.01    v2_pre_topc(sK1)),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f50,plain,(
% 2.20/1.01    l1_pre_topc(sK1)),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f57,plain,(
% 2.20/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f1,axiom,(
% 2.20/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.20/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.01  
% 2.20/1.01  fof(f10,plain,(
% 2.20/1.01    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.20/1.01    inference(ennf_transformation,[],[f1])).
% 2.20/1.01  
% 2.20/1.01  fof(f11,plain,(
% 2.20/1.01    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.20/1.01    inference(flattening,[],[f10])).
% 2.20/1.01  
% 2.20/1.01  fof(f37,plain,(
% 2.20/1.01    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.20/1.01    inference(cnf_transformation,[],[f11])).
% 2.20/1.01  
% 2.20/1.01  fof(f45,plain,(
% 2.20/1.01    ~v2_struct_0(sK0)),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f46,plain,(
% 2.20/1.01    v2_pre_topc(sK0)),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f47,plain,(
% 2.20/1.01    l1_pre_topc(sK0)),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f52,plain,(
% 2.20/1.01    m1_pre_topc(sK2,sK0)),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f65,plain,(
% 2.20/1.01    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f64,plain,(
% 2.20/1.01    sK6 = sK7),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f4,axiom,(
% 2.20/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 2.20/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.01  
% 2.20/1.01  fof(f15,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.20/1.01    inference(ennf_transformation,[],[f4])).
% 2.20/1.01  
% 2.20/1.01  fof(f16,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/1.01    inference(flattening,[],[f15])).
% 2.20/1.01  
% 2.20/1.01  fof(f40,plain,(
% 2.20/1.01    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/1.01    inference(cnf_transformation,[],[f16])).
% 2.20/1.01  
% 2.20/1.01  fof(f53,plain,(
% 2.20/1.01    ~v2_struct_0(sK3)),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f3,axiom,(
% 2.20/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.20/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.01  
% 2.20/1.01  fof(f14,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.20/1.01    inference(ennf_transformation,[],[f3])).
% 2.20/1.01  
% 2.20/1.01  fof(f39,plain,(
% 2.20/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.20/1.01    inference(cnf_transformation,[],[f14])).
% 2.20/1.01  
% 2.20/1.01  fof(f2,axiom,(
% 2.20/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.20/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.01  
% 2.20/1.01  fof(f12,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.20/1.01    inference(ennf_transformation,[],[f2])).
% 2.20/1.01  
% 2.20/1.01  fof(f13,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.20/1.01    inference(flattening,[],[f12])).
% 2.20/1.01  
% 2.20/1.01  fof(f38,plain,(
% 2.20/1.01    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/1.01    inference(cnf_transformation,[],[f13])).
% 2.20/1.01  
% 2.20/1.01  fof(f6,axiom,(
% 2.20/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.20/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.01  
% 2.20/1.01  fof(f19,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.20/1.01    inference(ennf_transformation,[],[f6])).
% 2.20/1.01  
% 2.20/1.01  fof(f20,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/1.01    inference(flattening,[],[f19])).
% 2.20/1.01  
% 2.20/1.01  fof(f25,plain,(
% 2.20/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/1.01    inference(nnf_transformation,[],[f20])).
% 2.20/1.01  
% 2.20/1.01  fof(f43,plain,(
% 2.20/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/1.01    inference(cnf_transformation,[],[f25])).
% 2.20/1.01  
% 2.20/1.01  fof(f67,plain,(
% 2.20/1.01    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/1.01    inference(equality_resolution,[],[f43])).
% 2.20/1.01  
% 2.20/1.01  fof(f63,plain,(
% 2.20/1.01    m1_connsp_2(sK5,sK3,sK6)),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f59,plain,(
% 2.20/1.01    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f60,plain,(
% 2.20/1.01    m1_subset_1(sK6,u1_struct_0(sK3))),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f51,plain,(
% 2.20/1.01    ~v2_struct_0(sK2)),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.01  
% 2.20/1.01  fof(f61,plain,(
% 2.20/1.01    m1_subset_1(sK7,u1_struct_0(sK2))),
% 2.20/1.01    inference(cnf_transformation,[],[f36])).
% 2.20/1.02  
% 2.20/1.02  fof(f66,plain,(
% 2.20/1.02    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)),
% 2.20/1.02    inference(cnf_transformation,[],[f36])).
% 2.20/1.02  
% 2.20/1.02  fof(f7,axiom,(
% 2.20/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 2.20/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.02  
% 2.20/1.02  fof(f21,plain,(
% 2.20/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.20/1.02    inference(ennf_transformation,[],[f7])).
% 2.20/1.02  
% 2.20/1.02  fof(f22,plain,(
% 2.20/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/1.02    inference(flattening,[],[f21])).
% 2.20/1.02  
% 2.20/1.02  fof(f44,plain,(
% 2.20/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/1.02    inference(cnf_transformation,[],[f22])).
% 2.20/1.02  
% 2.20/1.02  fof(f69,plain,(
% 2.20/1.02    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/1.02    inference(equality_resolution,[],[f44])).
% 2.20/1.02  
% 2.20/1.02  fof(f42,plain,(
% 2.20/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/1.02    inference(cnf_transformation,[],[f25])).
% 2.20/1.02  
% 2.20/1.02  fof(f68,plain,(
% 2.20/1.02    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/1.02    inference(equality_resolution,[],[f42])).
% 2.20/1.02  
% 2.20/1.02  fof(f62,plain,(
% 2.20/1.02    r1_tarski(sK5,u1_struct_0(sK2))),
% 2.20/1.02    inference(cnf_transformation,[],[f36])).
% 2.20/1.02  
% 2.20/1.02  cnf(c_20,negated_conjecture,
% 2.20/1.02      ( m1_pre_topc(sK3,sK0) ),
% 2.20/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1307,negated_conjecture,
% 2.20/1.02      ( m1_pre_topc(sK3,sK0) ),
% 2.20/1.02      inference(subtyping,[status(esa)],[c_20]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2009,plain,
% 2.20/1.02      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1307]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_16,negated_conjecture,
% 2.20/1.02      ( m1_pre_topc(sK2,sK3) ),
% 2.20/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1309,negated_conjecture,
% 2.20/1.02      ( m1_pre_topc(sK2,sK3) ),
% 2.20/1.02      inference(subtyping,[status(esa)],[c_16]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2007,plain,
% 2.20/1.02      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1309]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_4,plain,
% 2.20/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.20/1.02      | ~ m1_pre_topc(X3,X4)
% 2.20/1.02      | ~ m1_pre_topc(X3,X1)
% 2.20/1.02      | ~ m1_pre_topc(X1,X4)
% 2.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.20/1.02      | v2_struct_0(X4)
% 2.20/1.02      | v2_struct_0(X2)
% 2.20/1.02      | ~ l1_pre_topc(X4)
% 2.20/1.02      | ~ l1_pre_topc(X2)
% 2.20/1.02      | ~ v2_pre_topc(X4)
% 2.20/1.02      | ~ v2_pre_topc(X2)
% 2.20/1.02      | ~ v1_funct_1(X0)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.20/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_18,negated_conjecture,
% 2.20/1.02      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 2.20/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_644,plain,
% 2.20/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.20/1.02      | ~ m1_pre_topc(X0,X2)
% 2.20/1.02      | ~ m1_pre_topc(X1,X2)
% 2.20/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 2.20/1.02      | v2_struct_0(X4)
% 2.20/1.02      | v2_struct_0(X2)
% 2.20/1.02      | ~ l1_pre_topc(X4)
% 2.20/1.02      | ~ l1_pre_topc(X2)
% 2.20/1.02      | ~ v2_pre_topc(X4)
% 2.20/1.02      | ~ v2_pre_topc(X2)
% 2.20/1.02      | ~ v1_funct_1(X3)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(X4) != u1_struct_0(sK1)
% 2.20/1.02      | sK4 != X3 ),
% 2.20/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_18]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_645,plain,
% 2.20/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.20/1.02      | ~ m1_pre_topc(X0,X2)
% 2.20/1.02      | ~ m1_pre_topc(X1,X2)
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.20/1.02      | v2_struct_0(X2)
% 2.20/1.02      | v2_struct_0(X3)
% 2.20/1.02      | ~ l1_pre_topc(X2)
% 2.20/1.02      | ~ l1_pre_topc(X3)
% 2.20/1.02      | ~ v2_pre_topc(X2)
% 2.20/1.02      | ~ v2_pre_topc(X3)
% 2.20/1.02      | ~ v1_funct_1(sK4)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(unflattening,[status(thm)],[c_644]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_19,negated_conjecture,
% 2.20/1.02      ( v1_funct_1(sK4) ),
% 2.20/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_649,plain,
% 2.20/1.02      ( ~ v2_pre_topc(X3)
% 2.20/1.02      | ~ v2_pre_topc(X2)
% 2.20/1.02      | ~ l1_pre_topc(X3)
% 2.20/1.02      | ~ l1_pre_topc(X2)
% 2.20/1.02      | v2_struct_0(X3)
% 2.20/1.02      | v2_struct_0(X2)
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.20/1.02      | ~ m1_pre_topc(X1,X2)
% 2.20/1.02      | ~ m1_pre_topc(X0,X2)
% 2.20/1.02      | ~ m1_pre_topc(X0,X1)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(global_propositional_subsumption,
% 2.20/1.02                [status(thm)],
% 2.20/1.02                [c_645,c_19]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_650,plain,
% 2.20/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.20/1.02      | ~ m1_pre_topc(X0,X2)
% 2.20/1.02      | ~ m1_pre_topc(X1,X2)
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.20/1.02      | v2_struct_0(X2)
% 2.20/1.02      | v2_struct_0(X3)
% 2.20/1.02      | ~ l1_pre_topc(X2)
% 2.20/1.02      | ~ l1_pre_topc(X3)
% 2.20/1.02      | ~ v2_pre_topc(X2)
% 2.20/1.02      | ~ v2_pre_topc(X3)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(renaming,[status(thm)],[c_649]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1296,plain,
% 2.20/1.02      ( ~ m1_pre_topc(X0_55,X1_55)
% 2.20/1.02      | ~ m1_pre_topc(X0_55,X2_55)
% 2.20/1.02      | ~ m1_pre_topc(X1_55,X2_55)
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X3_55))))
% 2.20/1.02      | v2_struct_0(X2_55)
% 2.20/1.02      | v2_struct_0(X3_55)
% 2.20/1.02      | ~ l1_pre_topc(X2_55)
% 2.20/1.02      | ~ l1_pre_topc(X3_55)
% 2.20/1.02      | ~ v2_pre_topc(X2_55)
% 2.20/1.02      | ~ v2_pre_topc(X3_55)
% 2.20/1.02      | u1_struct_0(X1_55) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(X3_55) != u1_struct_0(sK1)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X1_55),u1_struct_0(X3_55),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X2_55,X3_55,X1_55,X0_55,sK4) ),
% 2.20/1.02      inference(subtyping,[status(esa)],[c_650]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2020,plain,
% 2.20/1.02      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK4,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,sK4)
% 2.20/1.02      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 2.20/1.02      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 2.20/1.02      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X3_55) = iProver_top
% 2.20/1.02      | v2_struct_0(X1_55) = iProver_top
% 2.20/1.02      | l1_pre_topc(X1_55) != iProver_top
% 2.20/1.02      | l1_pre_topc(X3_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(X1_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(X3_55) != iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1296]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3218,plain,
% 2.20/1.02      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4)
% 2.20/1.02      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,X2_55) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X2_55) = iProver_top
% 2.20/1.02      | v2_struct_0(sK1) = iProver_top
% 2.20/1.02      | l1_pre_topc(X2_55) != iProver_top
% 2.20/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.20/1.02      | v2_pre_topc(X2_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(sK1) != iProver_top ),
% 2.20/1.02      inference(equality_resolution,[status(thm)],[c_2020]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_26,negated_conjecture,
% 2.20/1.02      ( ~ v2_struct_0(sK1) ),
% 2.20/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_33,plain,
% 2.20/1.02      ( v2_struct_0(sK1) != iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_25,negated_conjecture,
% 2.20/1.02      ( v2_pre_topc(sK1) ),
% 2.20/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_34,plain,
% 2.20/1.02      ( v2_pre_topc(sK1) = iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_24,negated_conjecture,
% 2.20/1.02      ( l1_pre_topc(sK1) ),
% 2.20/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_35,plain,
% 2.20/1.02      ( l1_pre_topc(sK1) = iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1325,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2506,plain,
% 2.20/1.02      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 2.20/1.02      inference(instantiation,[status(thm)],[c_1325]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2584,plain,
% 2.20/1.02      ( ~ m1_pre_topc(X0_55,X1_55)
% 2.20/1.02      | ~ m1_pre_topc(X0_55,X2_55)
% 2.20/1.02      | ~ m1_pre_topc(X1_55,X2_55)
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(sK1))))
% 2.20/1.02      | v2_struct_0(X2_55)
% 2.20/1.02      | v2_struct_0(sK1)
% 2.20/1.02      | ~ l1_pre_topc(X2_55)
% 2.20/1.02      | ~ l1_pre_topc(sK1)
% 2.20/1.02      | ~ v2_pre_topc(X2_55)
% 2.20/1.02      | ~ v2_pre_topc(sK1)
% 2.20/1.02      | u1_struct_0(X1_55) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X1_55),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X2_55,sK1,X1_55,X0_55,sK4) ),
% 2.20/1.02      inference(instantiation,[status(thm)],[c_1296]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2585,plain,
% 2.20/1.02      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4)
% 2.20/1.02      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,X2_55) != iProver_top
% 2.20/1.02      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X2_55) = iProver_top
% 2.20/1.02      | v2_struct_0(sK1) = iProver_top
% 2.20/1.02      | l1_pre_topc(X2_55) != iProver_top
% 2.20/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.20/1.02      | v2_pre_topc(X2_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(sK1) != iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_2584]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3424,plain,
% 2.20/1.02      ( v2_pre_topc(X2_55) != iProver_top
% 2.20/1.02      | v2_struct_0(X2_55) = iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,X2_55) != iProver_top
% 2.20/1.02      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 2.20/1.02      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4)
% 2.20/1.02      | u1_struct_0(X0_55) != u1_struct_0(sK3)
% 2.20/1.02      | l1_pre_topc(X2_55) != iProver_top ),
% 2.20/1.02      inference(global_propositional_subsumption,
% 2.20/1.02                [status(thm)],
% 2.20/1.02                [c_3218,c_33,c_34,c_35,c_2506,c_2585]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3425,plain,
% 2.20/1.02      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4)
% 2.20/1.02      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,X2_55) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X2_55) = iProver_top
% 2.20/1.02      | l1_pre_topc(X2_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(X2_55) != iProver_top ),
% 2.20/1.02      inference(renaming,[status(thm)],[c_3424]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3439,plain,
% 2.20/1.02      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
% 2.20/1.02      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 2.20/1.02      | m1_pre_topc(X0_55,sK3) != iProver_top
% 2.20/1.02      | m1_pre_topc(sK3,X1_55) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X1_55) = iProver_top
% 2.20/1.02      | l1_pre_topc(X1_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(X1_55) != iProver_top ),
% 2.20/1.02      inference(equality_resolution,[status(thm)],[c_3425]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_17,negated_conjecture,
% 2.20/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.20/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1308,negated_conjecture,
% 2.20/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.20/1.02      inference(subtyping,[status(esa)],[c_17]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2008,plain,
% 2.20/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1308]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_0,plain,
% 2.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.20/1.02      | ~ v1_funct_1(X0)
% 2.20/1.02      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.20/1.02      inference(cnf_transformation,[],[f37]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_847,plain,
% 2.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.20/1.02      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 2.20/1.02      | sK4 != X0 ),
% 2.20/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_19]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_848,plain,
% 2.20/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.20/1.02      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 2.20/1.02      inference(unflattening,[status(thm)],[c_847]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1292,plain,
% 2.20/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.20/1.02      | k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54) ),
% 2.20/1.02      inference(subtyping,[status(esa)],[c_848]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2026,plain,
% 2.20/1.02      ( k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54)
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1292]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3027,plain,
% 2.20/1.02      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 2.20/1.02      inference(superposition,[status(thm)],[c_2008,c_2026]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3440,plain,
% 2.20/1.02      ( k3_tmap_1(X0_55,sK1,sK3,X1_55,sK4) = k7_relat_1(sK4,u1_struct_0(X1_55))
% 2.20/1.02      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,sK3) != iProver_top
% 2.20/1.02      | m1_pre_topc(sK3,X0_55) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | l1_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(X0_55) != iProver_top ),
% 2.20/1.02      inference(demodulation,[status(thm)],[c_3439,c_3027]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_42,plain,
% 2.20/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3445,plain,
% 2.20/1.02      ( m1_pre_topc(sK3,X0_55) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,sK3) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.20/1.02      | k3_tmap_1(X0_55,sK1,sK3,X1_55,sK4) = k7_relat_1(sK4,u1_struct_0(X1_55))
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | l1_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(X0_55) != iProver_top ),
% 2.20/1.02      inference(global_propositional_subsumption,
% 2.20/1.02                [status(thm)],
% 2.20/1.02                [c_3440,c_42]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3446,plain,
% 2.20/1.02      ( k3_tmap_1(X0_55,sK1,sK3,X1_55,sK4) = k7_relat_1(sK4,u1_struct_0(X1_55))
% 2.20/1.02      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,sK3) != iProver_top
% 2.20/1.02      | m1_pre_topc(sK3,X0_55) != iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | l1_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(X0_55) != iProver_top ),
% 2.20/1.02      inference(renaming,[status(thm)],[c_3445]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3458,plain,
% 2.20/1.02      ( k3_tmap_1(X0_55,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
% 2.20/1.02      | m1_pre_topc(sK3,X0_55) != iProver_top
% 2.20/1.02      | m1_pre_topc(sK2,X0_55) != iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | l1_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(X0_55) != iProver_top ),
% 2.20/1.02      inference(superposition,[status(thm)],[c_2007,c_3446]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3541,plain,
% 2.20/1.02      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
% 2.20/1.02      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.20/1.02      | v2_struct_0(sK0) = iProver_top
% 2.20/1.02      | l1_pre_topc(sK0) != iProver_top
% 2.20/1.02      | v2_pre_topc(sK0) != iProver_top ),
% 2.20/1.02      inference(superposition,[status(thm)],[c_2009,c_3458]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_29,negated_conjecture,
% 2.20/1.02      ( ~ v2_struct_0(sK0) ),
% 2.20/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_30,plain,
% 2.20/1.02      ( v2_struct_0(sK0) != iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_28,negated_conjecture,
% 2.20/1.02      ( v2_pre_topc(sK0) ),
% 2.20/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_31,plain,
% 2.20/1.02      ( v2_pre_topc(sK0) = iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_27,negated_conjecture,
% 2.20/1.02      ( l1_pre_topc(sK0) ),
% 2.20/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_32,plain,
% 2.20/1.02      ( l1_pre_topc(sK0) = iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_22,negated_conjecture,
% 2.20/1.02      ( m1_pre_topc(sK2,sK0) ),
% 2.20/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_37,plain,
% 2.20/1.02      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3544,plain,
% 2.20/1.02      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 2.20/1.02      inference(global_propositional_subsumption,
% 2.20/1.02                [status(thm)],
% 2.20/1.02                [c_3541,c_30,c_31,c_32,c_37]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_9,negated_conjecture,
% 2.20/1.02      ( r1_tmap_1(sK3,sK1,sK4,sK6)
% 2.20/1.02      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 2.20/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1315,negated_conjecture,
% 2.20/1.02      ( r1_tmap_1(sK3,sK1,sK4,sK6)
% 2.20/1.02      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 2.20/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2002,plain,
% 2.20/1.02      ( r1_tmap_1(sK3,sK1,sK4,sK6) = iProver_top
% 2.20/1.02      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1315]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_10,negated_conjecture,
% 2.20/1.02      ( sK6 = sK7 ),
% 2.20/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1314,negated_conjecture,
% 2.20/1.02      ( sK6 = sK7 ),
% 2.20/1.02      inference(subtyping,[status(esa)],[c_10]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2084,plain,
% 2.20/1.02      ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 2.20/1.02      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
% 2.20/1.02      inference(light_normalisation,[status(thm)],[c_2002,c_1314]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3547,plain,
% 2.20/1.02      ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 2.20/1.02      | r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),sK7) = iProver_top ),
% 2.20/1.02      inference(demodulation,[status(thm)],[c_3544,c_2084]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3,plain,
% 2.20/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.20/1.02      | ~ m1_pre_topc(X3,X1)
% 2.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X2)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(X2)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(X2)
% 2.20/1.02      | ~ v1_funct_1(X0)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.20/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_695,plain,
% 2.20/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X3)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(X3)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(X3)
% 2.20/1.02      | ~ v1_funct_1(X2)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(X3) != u1_struct_0(sK1)
% 2.20/1.02      | sK4 != X2 ),
% 2.20/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_18]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_696,plain,
% 2.20/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X2)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(X2)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(X2)
% 2.20/1.02      | ~ v1_funct_1(sK4)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(unflattening,[status(thm)],[c_695]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_700,plain,
% 2.20/1.02      ( ~ v2_pre_topc(X2)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(X2)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | v2_struct_0(X2)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.20/1.02      | ~ m1_pre_topc(X0,X1)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(global_propositional_subsumption,
% 2.20/1.02                [status(thm)],
% 2.20/1.02                [c_696,c_19]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_701,plain,
% 2.20/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X2)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(X2)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(X2)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(renaming,[status(thm)],[c_700]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1295,plain,
% 2.20/1.02      ( ~ m1_pre_topc(X0_55,X1_55)
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X2_55))))
% 2.20/1.02      | v2_struct_0(X1_55)
% 2.20/1.02      | v2_struct_0(X2_55)
% 2.20/1.02      | ~ l1_pre_topc(X1_55)
% 2.20/1.02      | ~ l1_pre_topc(X2_55)
% 2.20/1.02      | ~ v2_pre_topc(X1_55)
% 2.20/1.02      | ~ v2_pre_topc(X2_55)
% 2.20/1.02      | u1_struct_0(X1_55) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(X2_55) != u1_struct_0(sK1)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X1_55),u1_struct_0(X2_55),sK4,u1_struct_0(X0_55)) = k2_tmap_1(X1_55,X2_55,sK4,X0_55) ),
% 2.20/1.02      inference(subtyping,[status(esa)],[c_701]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2021,plain,
% 2.20/1.02      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK4,u1_struct_0(X2_55)) = k2_tmap_1(X0_55,X1_55,sK4,X2_55)
% 2.20/1.02      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | v2_struct_0(X1_55) = iProver_top
% 2.20/1.02      | l1_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | l1_pre_topc(X1_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(X1_55) != iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1295]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3200,plain,
% 2.20/1.02      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55)
% 2.20/1.02      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | v2_struct_0(sK1) = iProver_top
% 2.20/1.02      | l1_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.20/1.02      | v2_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(sK1) != iProver_top ),
% 2.20/1.02      inference(equality_resolution,[status(thm)],[c_2021]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2574,plain,
% 2.20/1.02      ( ~ m1_pre_topc(X0_55,X1_55)
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(sK1))))
% 2.20/1.02      | v2_struct_0(X1_55)
% 2.20/1.02      | v2_struct_0(sK1)
% 2.20/1.02      | ~ l1_pre_topc(X1_55)
% 2.20/1.02      | ~ l1_pre_topc(sK1)
% 2.20/1.02      | ~ v2_pre_topc(X1_55)
% 2.20/1.02      | ~ v2_pre_topc(sK1)
% 2.20/1.02      | u1_struct_0(X1_55) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X1_55),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k2_tmap_1(X1_55,sK1,sK4,X0_55) ),
% 2.20/1.02      inference(instantiation,[status(thm)],[c_1295]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2580,plain,
% 2.20/1.02      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55)
% 2.20/1.02      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | v2_struct_0(sK1) = iProver_top
% 2.20/1.02      | l1_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.20/1.02      | v2_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(sK1) != iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_2574]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3263,plain,
% 2.20/1.02      ( v2_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.20/1.02      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55)
% 2.20/1.02      | u1_struct_0(X0_55) != u1_struct_0(sK3)
% 2.20/1.02      | l1_pre_topc(X0_55) != iProver_top ),
% 2.20/1.02      inference(global_propositional_subsumption,
% 2.20/1.02                [status(thm)],
% 2.20/1.02                [c_3200,c_33,c_34,c_35,c_2506,c_2580]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3264,plain,
% 2.20/1.02      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 2.20/1.02      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55)
% 2.20/1.02      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | l1_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(X0_55) != iProver_top ),
% 2.20/1.02      inference(renaming,[status(thm)],[c_3263]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3276,plain,
% 2.20/1.02      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k2_tmap_1(sK3,sK1,sK4,X0_55)
% 2.20/1.02      | m1_pre_topc(X0_55,sK3) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.20/1.02      | v2_struct_0(sK3) = iProver_top
% 2.20/1.02      | l1_pre_topc(sK3) != iProver_top
% 2.20/1.02      | v2_pre_topc(sK3) != iProver_top ),
% 2.20/1.02      inference(equality_resolution,[status(thm)],[c_3264]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3277,plain,
% 2.20/1.02      ( k2_tmap_1(sK3,sK1,sK4,X0_55) = k7_relat_1(sK4,u1_struct_0(X0_55))
% 2.20/1.02      | m1_pre_topc(X0_55,sK3) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.20/1.02      | v2_struct_0(sK3) = iProver_top
% 2.20/1.02      | l1_pre_topc(sK3) != iProver_top
% 2.20/1.02      | v2_pre_topc(sK3) != iProver_top ),
% 2.20/1.02      inference(demodulation,[status(thm)],[c_3276,c_3027]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_21,negated_conjecture,
% 2.20/1.02      ( ~ v2_struct_0(sK3) ),
% 2.20/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_38,plain,
% 2.20/1.02      ( v2_struct_0(sK3) != iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_39,plain,
% 2.20/1.02      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2,plain,
% 2.20/1.02      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.20/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1317,plain,
% 2.20/1.02      ( ~ m1_pre_topc(X0_55,X1_55)
% 2.20/1.02      | ~ l1_pre_topc(X1_55)
% 2.20/1.02      | l1_pre_topc(X0_55) ),
% 2.20/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2346,plain,
% 2.20/1.02      ( ~ m1_pre_topc(X0_55,sK0)
% 2.20/1.02      | l1_pre_topc(X0_55)
% 2.20/1.02      | ~ l1_pre_topc(sK0) ),
% 2.20/1.02      inference(instantiation,[status(thm)],[c_1317]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2347,plain,
% 2.20/1.02      ( m1_pre_topc(X0_55,sK0) != iProver_top
% 2.20/1.02      | l1_pre_topc(X0_55) = iProver_top
% 2.20/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_2346]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2349,plain,
% 2.20/1.02      ( m1_pre_topc(sK3,sK0) != iProver_top
% 2.20/1.02      | l1_pre_topc(sK3) = iProver_top
% 2.20/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 2.20/1.02      inference(instantiation,[status(thm)],[c_2347]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1,plain,
% 2.20/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | v2_pre_topc(X0) ),
% 2.20/1.02      inference(cnf_transformation,[],[f38]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1318,plain,
% 2.20/1.02      ( ~ m1_pre_topc(X0_55,X1_55)
% 2.20/1.02      | ~ l1_pre_topc(X1_55)
% 2.20/1.02      | ~ v2_pre_topc(X1_55)
% 2.20/1.02      | v2_pre_topc(X0_55) ),
% 2.20/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2360,plain,
% 2.20/1.02      ( ~ m1_pre_topc(X0_55,sK0)
% 2.20/1.02      | ~ l1_pre_topc(sK0)
% 2.20/1.02      | v2_pre_topc(X0_55)
% 2.20/1.02      | ~ v2_pre_topc(sK0) ),
% 2.20/1.02      inference(instantiation,[status(thm)],[c_1318]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2361,plain,
% 2.20/1.02      ( m1_pre_topc(X0_55,sK0) != iProver_top
% 2.20/1.02      | l1_pre_topc(sK0) != iProver_top
% 2.20/1.02      | v2_pre_topc(X0_55) = iProver_top
% 2.20/1.02      | v2_pre_topc(sK0) != iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_2360]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2363,plain,
% 2.20/1.02      ( m1_pre_topc(sK3,sK0) != iProver_top
% 2.20/1.02      | l1_pre_topc(sK0) != iProver_top
% 2.20/1.02      | v2_pre_topc(sK3) = iProver_top
% 2.20/1.02      | v2_pre_topc(sK0) != iProver_top ),
% 2.20/1.02      inference(instantiation,[status(thm)],[c_2361]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3282,plain,
% 2.20/1.02      ( k2_tmap_1(sK3,sK1,sK4,X0_55) = k7_relat_1(sK4,u1_struct_0(X0_55))
% 2.20/1.02      | m1_pre_topc(X0_55,sK3) != iProver_top ),
% 2.20/1.02      inference(global_propositional_subsumption,
% 2.20/1.02                [status(thm)],
% 2.20/1.02                [c_3277,c_31,c_32,c_38,c_39,c_42,c_2349,c_2363]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3290,plain,
% 2.20/1.02      ( k2_tmap_1(sK3,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 2.20/1.02      inference(superposition,[status(thm)],[c_2007,c_3282]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_5,plain,
% 2.20/1.02      ( r1_tmap_1(X0,X1,X2,X3)
% 2.20/1.02      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.20/1.02      | ~ m1_connsp_2(X5,X0,X3)
% 2.20/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.20/1.02      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.20/1.02      | ~ m1_pre_topc(X4,X0)
% 2.20/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.20/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.20/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(X4)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(X0)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(X0)
% 2.20/1.02      | ~ v1_funct_1(X2) ),
% 2.20/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_11,negated_conjecture,
% 2.20/1.02      ( m1_connsp_2(sK5,sK3,sK6) ),
% 2.20/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_422,plain,
% 2.20/1.02      ( r1_tmap_1(X0,X1,X2,X3)
% 2.20/1.02      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.20/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.20/1.02      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.20/1.02      | ~ m1_pre_topc(X4,X0)
% 2.20/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.20/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.20/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X4)
% 2.20/1.02      | ~ l1_pre_topc(X0)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(X0)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v1_funct_1(X2)
% 2.20/1.02      | sK5 != X5
% 2.20/1.02      | sK6 != X3
% 2.20/1.02      | sK3 != X0 ),
% 2.20/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_11]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_423,plain,
% 2.20/1.02      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
% 2.20/1.02      | r1_tmap_1(sK3,X1,X2,sK6)
% 2.20/1.02      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_pre_topc(X0,sK3)
% 2.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.20/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(sK3)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(sK3)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(sK3)
% 2.20/1.02      | ~ v1_funct_1(X2) ),
% 2.20/1.02      inference(unflattening,[status(thm)],[c_422]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_15,negated_conjecture,
% 2.20/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.20/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_14,negated_conjecture,
% 2.20/1.02      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.20/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_427,plain,
% 2.20/1.02      ( v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.20/1.02      | ~ m1_pre_topc(X0,sK3)
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.20/1.02      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
% 2.20/1.02      | r1_tmap_1(sK3,X1,X2,sK6)
% 2.20/1.02      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(sK3)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(sK3)
% 2.20/1.02      | ~ v1_funct_1(X2) ),
% 2.20/1.02      inference(global_propositional_subsumption,
% 2.20/1.02                [status(thm)],
% 2.20/1.02                [c_423,c_21,c_15,c_14]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_428,plain,
% 2.20/1.02      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
% 2.20/1.02      | r1_tmap_1(sK3,X1,X2,sK6)
% 2.20/1.02      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_pre_topc(X0,sK3)
% 2.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(sK3)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(sK3)
% 2.20/1.02      | ~ v1_funct_1(X2) ),
% 2.20/1.02      inference(renaming,[status(thm)],[c_427]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_740,plain,
% 2.20/1.02      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
% 2.20/1.02      | r1_tmap_1(sK3,X1,X2,sK6)
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_pre_topc(X0,sK3)
% 2.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(sK3)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(sK3)
% 2.20/1.02      | ~ v1_funct_1(X2)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.20/1.02      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.20/1.02      | sK4 != X2 ),
% 2.20/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_428]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_741,plain,
% 2.20/1.02      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
% 2.20/1.02      | r1_tmap_1(sK3,X1,sK4,sK6)
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_pre_topc(X0,sK3)
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(sK3)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(sK3)
% 2.20/1.02      | ~ v1_funct_1(sK4)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(unflattening,[status(thm)],[c_740]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_745,plain,
% 2.20/1.02      ( ~ v2_pre_topc(sK3)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(sK3)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_pre_topc(X0,sK3)
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.20/1.02      | r1_tmap_1(sK3,X1,sK4,sK6)
% 2.20/1.02      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(global_propositional_subsumption,
% 2.20/1.02                [status(thm)],
% 2.20/1.02                [c_741,c_19]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_746,plain,
% 2.20/1.02      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
% 2.20/1.02      | r1_tmap_1(sK3,X1,sK4,sK6)
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_pre_topc(X0,sK3)
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(sK3)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(sK3)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(renaming,[status(thm)],[c_745]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1294,plain,
% 2.20/1.02      ( ~ r1_tmap_1(X0_55,X1_55,k2_tmap_1(sK3,X1_55,sK4,X0_55),sK6)
% 2.20/1.02      | r1_tmap_1(sK3,X1_55,sK4,sK6)
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0_55))
% 2.20/1.02      | ~ m1_pre_topc(X0_55,sK3)
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0_55))
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_55))))
% 2.20/1.02      | v2_struct_0(X0_55)
% 2.20/1.02      | v2_struct_0(X1_55)
% 2.20/1.02      | ~ l1_pre_topc(X1_55)
% 2.20/1.02      | ~ l1_pre_topc(sK3)
% 2.20/1.02      | ~ v2_pre_topc(X1_55)
% 2.20/1.02      | ~ v2_pre_topc(sK3)
% 2.20/1.02      | u1_struct_0(X1_55) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(subtyping,[status(esa)],[c_746]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1319,plain,
% 2.20/1.02      ( ~ r1_tmap_1(X0_55,X1_55,k2_tmap_1(sK3,X1_55,sK4,X0_55),sK6)
% 2.20/1.02      | r1_tmap_1(sK3,X1_55,sK4,sK6)
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0_55))
% 2.20/1.02      | ~ m1_pre_topc(X0_55,sK3)
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0_55))
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_55))))
% 2.20/1.02      | v2_struct_0(X0_55)
% 2.20/1.02      | v2_struct_0(X1_55)
% 2.20/1.02      | ~ l1_pre_topc(X1_55)
% 2.20/1.02      | ~ v2_pre_topc(X1_55)
% 2.20/1.02      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 2.20/1.02      | ~ sP0_iProver_split ),
% 2.20/1.02      inference(splitting,
% 2.20/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.20/1.02                [c_1294]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2023,plain,
% 2.20/1.02      ( u1_struct_0(X0_55) != u1_struct_0(sK1)
% 2.20/1.02      | r1_tmap_1(X1_55,X0_55,k2_tmap_1(sK3,X0_55,sK4,X1_55),sK6) != iProver_top
% 2.20/1.02      | r1_tmap_1(sK3,X0_55,sK4,sK6) = iProver_top
% 2.20/1.02      | r1_tarski(sK5,u1_struct_0(X1_55)) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,sK3) != iProver_top
% 2.20/1.02      | m1_subset_1(sK6,u1_struct_0(X1_55)) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | v2_struct_0(X1_55) = iProver_top
% 2.20/1.02      | l1_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | sP0_iProver_split != iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1319]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2124,plain,
% 2.20/1.02      ( u1_struct_0(X0_55) != u1_struct_0(sK1)
% 2.20/1.02      | r1_tmap_1(X1_55,X0_55,k2_tmap_1(sK3,X0_55,sK4,X1_55),sK7) != iProver_top
% 2.20/1.02      | r1_tmap_1(sK3,X0_55,sK4,sK7) = iProver_top
% 2.20/1.02      | r1_tarski(sK5,u1_struct_0(X1_55)) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,sK3) != iProver_top
% 2.20/1.02      | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X1_55) = iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | l1_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | sP0_iProver_split != iProver_top ),
% 2.20/1.02      inference(light_normalisation,[status(thm)],[c_2023,c_1314]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1320,plain,
% 2.20/1.02      ( ~ l1_pre_topc(sK3) | ~ v2_pre_topc(sK3) | sP0_iProver_split ),
% 2.20/1.02      inference(splitting,
% 2.20/1.02                [splitting(split),new_symbols(definition,[])],
% 2.20/1.02                [c_1294]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1378,plain,
% 2.20/1.02      ( l1_pre_topc(sK3) != iProver_top
% 2.20/1.02      | v2_pre_topc(sK3) != iProver_top
% 2.20/1.02      | sP0_iProver_split = iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1320]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2716,plain,
% 2.20/1.02      ( v2_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | l1_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | v2_struct_0(X1_55) = iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.20/1.02      | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,sK3) != iProver_top
% 2.20/1.02      | r1_tarski(sK5,u1_struct_0(X1_55)) != iProver_top
% 2.20/1.02      | r1_tmap_1(sK3,X0_55,sK4,sK7) = iProver_top
% 2.20/1.02      | r1_tmap_1(X1_55,X0_55,k2_tmap_1(sK3,X0_55,sK4,X1_55),sK7) != iProver_top
% 2.20/1.02      | u1_struct_0(X0_55) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(global_propositional_subsumption,
% 2.20/1.02                [status(thm)],
% 2.20/1.02                [c_2124,c_31,c_32,c_39,c_1378,c_2349,c_2363]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2717,plain,
% 2.20/1.02      ( u1_struct_0(X0_55) != u1_struct_0(sK1)
% 2.20/1.02      | r1_tmap_1(X1_55,X0_55,k2_tmap_1(sK3,X0_55,sK4,X1_55),sK7) != iProver_top
% 2.20/1.02      | r1_tmap_1(sK3,X0_55,sK4,sK7) = iProver_top
% 2.20/1.02      | r1_tarski(sK5,u1_struct_0(X1_55)) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,sK3) != iProver_top
% 2.20/1.02      | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X1_55) = iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | l1_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(X0_55) != iProver_top ),
% 2.20/1.02      inference(renaming,[status(thm)],[c_2716]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2733,plain,
% 2.20/1.02      ( r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) != iProver_top
% 2.20/1.02      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 2.20/1.02      | r1_tarski(sK5,u1_struct_0(X0_55)) != iProver_top
% 2.20/1.02      | m1_pre_topc(X0_55,sK3) != iProver_top
% 2.20/1.02      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | v2_struct_0(sK1) = iProver_top
% 2.20/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.20/1.02      | v2_pre_topc(sK1) != iProver_top ),
% 2.20/1.02      inference(equality_resolution,[status(thm)],[c_2717]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_23,negated_conjecture,
% 2.20/1.02      ( ~ v2_struct_0(sK2) ),
% 2.20/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_36,plain,
% 2.20/1.02      ( v2_struct_0(sK2) != iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_43,plain,
% 2.20/1.02      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_13,negated_conjecture,
% 2.20/1.02      ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
% 2.20/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_46,plain,
% 2.20/1.02      ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1311,negated_conjecture,
% 2.20/1.02      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.20/1.02      inference(subtyping,[status(esa)],[c_14]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2005,plain,
% 2.20/1.02      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1311]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2055,plain,
% 2.20/1.02      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.20/1.02      inference(light_normalisation,[status(thm)],[c_2005,c_1314]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_8,negated_conjecture,
% 2.20/1.02      ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
% 2.20/1.02      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 2.20/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1316,negated_conjecture,
% 2.20/1.02      ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
% 2.20/1.02      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 2.20/1.02      inference(subtyping,[status(esa)],[c_8]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2001,plain,
% 2.20/1.02      ( r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top
% 2.20/1.02      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1316]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2089,plain,
% 2.20/1.02      ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 2.20/1.02      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
% 2.20/1.02      inference(light_normalisation,[status(thm)],[c_2001,c_1314]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2496,plain,
% 2.20/1.02      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 2.20/1.02      inference(instantiation,[status(thm)],[c_1325]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_7,plain,
% 2.20/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.20/1.02      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.20/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.20/1.02      | ~ m1_pre_topc(X4,X5)
% 2.20/1.02      | ~ m1_pre_topc(X4,X0)
% 2.20/1.02      | ~ m1_pre_topc(X0,X5)
% 2.20/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.20/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.20/1.02      | v2_struct_0(X5)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(X4)
% 2.20/1.02      | ~ l1_pre_topc(X5)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(X5)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v1_funct_1(X2) ),
% 2.20/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_578,plain,
% 2.20/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.20/1.02      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.20/1.02      | ~ m1_pre_topc(X4,X0)
% 2.20/1.02      | ~ m1_pre_topc(X4,X5)
% 2.20/1.02      | ~ m1_pre_topc(X0,X5)
% 2.20/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.20/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X4)
% 2.20/1.02      | v2_struct_0(X5)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(X5)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(X5)
% 2.20/1.02      | ~ v1_funct_1(X2)
% 2.20/1.02      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.20/1.02      | sK4 != X2 ),
% 2.20/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_579,plain,
% 2.20/1.02      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.20/1.02      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.20/1.02      | ~ m1_pre_topc(X0,X3)
% 2.20/1.02      | ~ m1_pre_topc(X0,X2)
% 2.20/1.02      | ~ m1_pre_topc(X3,X2)
% 2.20/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.20/1.02      | v2_struct_0(X3)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(X2)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(X2)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(X2)
% 2.20/1.02      | ~ v1_funct_1(sK4)
% 2.20/1.02      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(unflattening,[status(thm)],[c_578]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_583,plain,
% 2.20/1.02      ( ~ v2_pre_topc(X2)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(X2)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | v2_struct_0(X2)
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X3)
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.20/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.20/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_pre_topc(X3,X2)
% 2.20/1.02      | ~ m1_pre_topc(X0,X2)
% 2.20/1.02      | ~ m1_pre_topc(X0,X3)
% 2.20/1.02      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.20/1.02      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.20/1.02      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(global_propositional_subsumption,
% 2.20/1.02                [status(thm)],
% 2.20/1.02                [c_579,c_19]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_584,plain,
% 2.20/1.02      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.20/1.02      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.20/1.02      | ~ m1_pre_topc(X3,X2)
% 2.20/1.02      | ~ m1_pre_topc(X0,X3)
% 2.20/1.02      | ~ m1_pre_topc(X0,X2)
% 2.20/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X2)
% 2.20/1.02      | v2_struct_0(X3)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(X2)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(X2)
% 2.20/1.02      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(renaming,[status(thm)],[c_583]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1297,plain,
% 2.20/1.02      ( r1_tmap_1(X0_55,X1_55,k3_tmap_1(X2_55,X1_55,X3_55,X0_55,sK4),X0_53)
% 2.20/1.02      | ~ r1_tmap_1(X3_55,X1_55,sK4,X0_53)
% 2.20/1.02      | ~ m1_pre_topc(X0_55,X2_55)
% 2.20/1.02      | ~ m1_pre_topc(X3_55,X2_55)
% 2.20/1.02      | ~ m1_pre_topc(X0_55,X3_55)
% 2.20/1.02      | ~ m1_subset_1(X0_53,u1_struct_0(X0_55))
% 2.20/1.02      | ~ m1_subset_1(X0_53,u1_struct_0(X3_55))
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_55),u1_struct_0(X1_55))))
% 2.20/1.02      | v2_struct_0(X0_55)
% 2.20/1.02      | v2_struct_0(X1_55)
% 2.20/1.02      | v2_struct_0(X2_55)
% 2.20/1.02      | v2_struct_0(X3_55)
% 2.20/1.02      | ~ l1_pre_topc(X1_55)
% 2.20/1.02      | ~ l1_pre_topc(X2_55)
% 2.20/1.02      | ~ v2_pre_topc(X1_55)
% 2.20/1.02      | ~ v2_pre_topc(X2_55)
% 2.20/1.02      | u1_struct_0(X3_55) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(X1_55) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(subtyping,[status(esa)],[c_584]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2331,plain,
% 2.20/1.02      ( r1_tmap_1(X0_55,sK1,k3_tmap_1(X1_55,sK1,X2_55,X0_55,sK4),X0_53)
% 2.20/1.02      | ~ r1_tmap_1(X2_55,sK1,sK4,X0_53)
% 2.20/1.02      | ~ m1_pre_topc(X0_55,X1_55)
% 2.20/1.02      | ~ m1_pre_topc(X0_55,X2_55)
% 2.20/1.02      | ~ m1_pre_topc(X2_55,X1_55)
% 2.20/1.02      | ~ m1_subset_1(X0_53,u1_struct_0(X0_55))
% 2.20/1.02      | ~ m1_subset_1(X0_53,u1_struct_0(X2_55))
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(sK1))))
% 2.20/1.02      | v2_struct_0(X0_55)
% 2.20/1.02      | v2_struct_0(X1_55)
% 2.20/1.02      | v2_struct_0(X2_55)
% 2.20/1.02      | v2_struct_0(sK1)
% 2.20/1.02      | ~ l1_pre_topc(X1_55)
% 2.20/1.02      | ~ l1_pre_topc(sK1)
% 2.20/1.02      | ~ v2_pre_topc(X1_55)
% 2.20/1.02      | ~ v2_pre_topc(sK1)
% 2.20/1.02      | u1_struct_0(X2_55) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(instantiation,[status(thm)],[c_1297]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2599,plain,
% 2.20/1.02      ( ~ r1_tmap_1(X0_55,sK1,sK4,X0_53)
% 2.20/1.02      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X0_55,sK2,sK4),X0_53)
% 2.20/1.02      | ~ m1_pre_topc(X0_55,sK0)
% 2.20/1.02      | ~ m1_pre_topc(sK2,X0_55)
% 2.20/1.02      | ~ m1_pre_topc(sK2,sK0)
% 2.20/1.02      | ~ m1_subset_1(X0_53,u1_struct_0(X0_55))
% 2.20/1.02      | ~ m1_subset_1(X0_53,u1_struct_0(sK2))
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1))))
% 2.20/1.02      | v2_struct_0(X0_55)
% 2.20/1.02      | v2_struct_0(sK0)
% 2.20/1.02      | v2_struct_0(sK1)
% 2.20/1.02      | v2_struct_0(sK2)
% 2.20/1.02      | ~ l1_pre_topc(sK0)
% 2.20/1.02      | ~ l1_pre_topc(sK1)
% 2.20/1.02      | ~ v2_pre_topc(sK0)
% 2.20/1.02      | ~ v2_pre_topc(sK1)
% 2.20/1.02      | u1_struct_0(X0_55) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(instantiation,[status(thm)],[c_2331]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2991,plain,
% 2.20/1.02      ( ~ r1_tmap_1(X0_55,sK1,sK4,sK7)
% 2.20/1.02      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X0_55,sK2,sK4),sK7)
% 2.20/1.02      | ~ m1_pre_topc(X0_55,sK0)
% 2.20/1.02      | ~ m1_pre_topc(sK2,X0_55)
% 2.20/1.02      | ~ m1_pre_topc(sK2,sK0)
% 2.20/1.02      | ~ m1_subset_1(sK7,u1_struct_0(X0_55))
% 2.20/1.02      | ~ m1_subset_1(sK7,u1_struct_0(sK2))
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1))))
% 2.20/1.02      | v2_struct_0(X0_55)
% 2.20/1.02      | v2_struct_0(sK0)
% 2.20/1.02      | v2_struct_0(sK1)
% 2.20/1.02      | v2_struct_0(sK2)
% 2.20/1.02      | ~ l1_pre_topc(sK0)
% 2.20/1.02      | ~ l1_pre_topc(sK1)
% 2.20/1.02      | ~ v2_pre_topc(sK0)
% 2.20/1.02      | ~ v2_pre_topc(sK1)
% 2.20/1.02      | u1_struct_0(X0_55) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(instantiation,[status(thm)],[c_2599]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2992,plain,
% 2.20/1.02      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.20/1.02      | r1_tmap_1(X0_55,sK1,sK4,sK7) != iProver_top
% 2.20/1.02      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X0_55,sK2,sK4),sK7) = iProver_top
% 2.20/1.02      | m1_pre_topc(X0_55,sK0) != iProver_top
% 2.20/1.02      | m1_pre_topc(sK2,X0_55) != iProver_top
% 2.20/1.02      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.20/1.02      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 2.20/1.02      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | v2_struct_0(sK0) = iProver_top
% 2.20/1.02      | v2_struct_0(sK1) = iProver_top
% 2.20/1.02      | v2_struct_0(sK2) = iProver_top
% 2.20/1.02      | l1_pre_topc(sK0) != iProver_top
% 2.20/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.20/1.02      | v2_pre_topc(sK0) != iProver_top
% 2.20/1.02      | v2_pre_topc(sK1) != iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_2991]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2994,plain,
% 2.20/1.02      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.20/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.20/1.02      | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 2.20/1.02      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top
% 2.20/1.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.20/1.02      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.20/1.02      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.20/1.02      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.20/1.02      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.20/1.02      | v2_struct_0(sK3) = iProver_top
% 2.20/1.02      | v2_struct_0(sK0) = iProver_top
% 2.20/1.02      | v2_struct_0(sK1) = iProver_top
% 2.20/1.02      | v2_struct_0(sK2) = iProver_top
% 2.20/1.02      | l1_pre_topc(sK0) != iProver_top
% 2.20/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.20/1.02      | v2_pre_topc(sK0) != iProver_top
% 2.20/1.02      | v2_pre_topc(sK1) != iProver_top ),
% 2.20/1.02      inference(instantiation,[status(thm)],[c_2992]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3122,plain,
% 2.20/1.02      ( v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) != iProver_top
% 2.20/1.02      | r1_tarski(sK5,u1_struct_0(X0_55)) != iProver_top
% 2.20/1.02      | m1_pre_topc(X0_55,sK3) != iProver_top
% 2.20/1.02      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top ),
% 2.20/1.02      inference(global_propositional_subsumption,
% 2.20/1.02                [status(thm)],
% 2.20/1.02                [c_2733,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,
% 2.20/1.02                 c_39,c_42,c_43,c_46,c_2055,c_2089,c_2496,c_2506,c_2994]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3123,plain,
% 2.20/1.02      ( r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) != iProver_top
% 2.20/1.02      | r1_tarski(sK5,u1_struct_0(X0_55)) != iProver_top
% 2.20/1.02      | m1_pre_topc(X0_55,sK3) != iProver_top
% 2.20/1.02      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top ),
% 2.20/1.02      inference(renaming,[status(thm)],[c_3122]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3357,plain,
% 2.20/1.02      ( r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),sK7) != iProver_top
% 2.20/1.02      | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
% 2.20/1.02      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.20/1.02      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
% 2.20/1.02      | v2_struct_0(sK2) = iProver_top ),
% 2.20/1.02      inference(superposition,[status(thm)],[c_3290,c_3123]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_6,plain,
% 2.20/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.20/1.02      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.20/1.02      | ~ m1_connsp_2(X5,X0,X3)
% 2.20/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.20/1.02      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.20/1.02      | ~ m1_pre_topc(X4,X0)
% 2.20/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.20/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.20/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(X4)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(X0)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(X0)
% 2.20/1.02      | ~ v1_funct_1(X2) ),
% 2.20/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_368,plain,
% 2.20/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.20/1.02      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.20/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.20/1.02      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.20/1.02      | ~ m1_pre_topc(X4,X0)
% 2.20/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.20/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.20/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X4)
% 2.20/1.02      | ~ l1_pre_topc(X0)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(X0)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v1_funct_1(X2)
% 2.20/1.02      | sK5 != X5
% 2.20/1.02      | sK6 != X3
% 2.20/1.02      | sK3 != X0 ),
% 2.20/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_11]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_369,plain,
% 2.20/1.02      ( r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
% 2.20/1.02      | ~ r1_tmap_1(sK3,X1,X2,sK6)
% 2.20/1.02      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_pre_topc(X0,sK3)
% 2.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.20/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(sK3)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(sK3)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(sK3)
% 2.20/1.02      | ~ v1_funct_1(X2) ),
% 2.20/1.02      inference(unflattening,[status(thm)],[c_368]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_373,plain,
% 2.20/1.02      ( v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.20/1.02      | ~ m1_pre_topc(X0,sK3)
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.20/1.02      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
% 2.20/1.02      | ~ r1_tmap_1(sK3,X1,X2,sK6)
% 2.20/1.02      | r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(sK3)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(sK3)
% 2.20/1.02      | ~ v1_funct_1(X2) ),
% 2.20/1.02      inference(global_propositional_subsumption,
% 2.20/1.02                [status(thm)],
% 2.20/1.02                [c_369,c_21,c_15,c_14]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_374,plain,
% 2.20/1.02      ( r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
% 2.20/1.02      | ~ r1_tmap_1(sK3,X1,X2,sK6)
% 2.20/1.02      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_pre_topc(X0,sK3)
% 2.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(sK3)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(sK3)
% 2.20/1.02      | ~ v1_funct_1(X2) ),
% 2.20/1.02      inference(renaming,[status(thm)],[c_373]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_791,plain,
% 2.20/1.02      ( r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
% 2.20/1.02      | ~ r1_tmap_1(sK3,X1,X2,sK6)
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_pre_topc(X0,sK3)
% 2.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(sK3)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(sK3)
% 2.20/1.02      | ~ v1_funct_1(X2)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.20/1.02      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.20/1.02      | sK4 != X2 ),
% 2.20/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_374]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_792,plain,
% 2.20/1.02      ( r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
% 2.20/1.02      | ~ r1_tmap_1(sK3,X1,sK4,sK6)
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_pre_topc(X0,sK3)
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(sK3)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(sK3)
% 2.20/1.02      | ~ v1_funct_1(sK4)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(unflattening,[status(thm)],[c_791]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_796,plain,
% 2.20/1.02      ( ~ v2_pre_topc(sK3)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(sK3)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_pre_topc(X0,sK3)
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.20/1.02      | ~ r1_tmap_1(sK3,X1,sK4,sK6)
% 2.20/1.02      | r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(global_propositional_subsumption,
% 2.20/1.02                [status(thm)],
% 2.20/1.02                [c_792,c_19]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_797,plain,
% 2.20/1.02      ( r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
% 2.20/1.02      | ~ r1_tmap_1(sK3,X1,sK4,sK6)
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_pre_topc(X0,sK3)
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.20/1.02      | v2_struct_0(X0)
% 2.20/1.02      | v2_struct_0(X1)
% 2.20/1.02      | ~ l1_pre_topc(X1)
% 2.20/1.02      | ~ l1_pre_topc(sK3)
% 2.20/1.02      | ~ v2_pre_topc(X1)
% 2.20/1.02      | ~ v2_pre_topc(sK3)
% 2.20/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(renaming,[status(thm)],[c_796]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1293,plain,
% 2.20/1.02      ( r1_tmap_1(X0_55,X1_55,k2_tmap_1(sK3,X1_55,sK4,X0_55),sK6)
% 2.20/1.02      | ~ r1_tmap_1(sK3,X1_55,sK4,sK6)
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0_55))
% 2.20/1.02      | ~ m1_pre_topc(X0_55,sK3)
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0_55))
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_55))))
% 2.20/1.02      | v2_struct_0(X0_55)
% 2.20/1.02      | v2_struct_0(X1_55)
% 2.20/1.02      | ~ l1_pre_topc(X1_55)
% 2.20/1.02      | ~ l1_pre_topc(sK3)
% 2.20/1.02      | ~ v2_pre_topc(X1_55)
% 2.20/1.02      | ~ v2_pre_topc(sK3)
% 2.20/1.02      | u1_struct_0(X1_55) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(subtyping,[status(esa)],[c_797]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1321,plain,
% 2.20/1.02      ( r1_tmap_1(X0_55,X1_55,k2_tmap_1(sK3,X1_55,sK4,X0_55),sK6)
% 2.20/1.02      | ~ r1_tmap_1(sK3,X1_55,sK4,sK6)
% 2.20/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0_55))
% 2.20/1.02      | ~ m1_pre_topc(X0_55,sK3)
% 2.20/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0_55))
% 2.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_55))))
% 2.20/1.02      | v2_struct_0(X0_55)
% 2.20/1.02      | v2_struct_0(X1_55)
% 2.20/1.02      | ~ l1_pre_topc(X1_55)
% 2.20/1.02      | ~ v2_pre_topc(X1_55)
% 2.20/1.02      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 2.20/1.02      | ~ sP1_iProver_split ),
% 2.20/1.02      inference(splitting,
% 2.20/1.02                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.20/1.02                [c_1293]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2025,plain,
% 2.20/1.02      ( u1_struct_0(X0_55) != u1_struct_0(sK1)
% 2.20/1.02      | r1_tmap_1(X1_55,X0_55,k2_tmap_1(sK3,X0_55,sK4,X1_55),sK6) = iProver_top
% 2.20/1.02      | r1_tmap_1(sK3,X0_55,sK4,sK6) != iProver_top
% 2.20/1.02      | r1_tarski(sK5,u1_struct_0(X1_55)) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,sK3) != iProver_top
% 2.20/1.02      | m1_subset_1(sK6,u1_struct_0(X1_55)) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | v2_struct_0(X1_55) = iProver_top
% 2.20/1.02      | l1_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | sP1_iProver_split != iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1321]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2149,plain,
% 2.20/1.02      ( u1_struct_0(X0_55) != u1_struct_0(sK1)
% 2.20/1.02      | r1_tmap_1(X1_55,X0_55,k2_tmap_1(sK3,X0_55,sK4,X1_55),sK7) = iProver_top
% 2.20/1.02      | r1_tmap_1(sK3,X0_55,sK4,sK7) != iProver_top
% 2.20/1.02      | r1_tarski(sK5,u1_struct_0(X1_55)) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,sK3) != iProver_top
% 2.20/1.02      | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X1_55) = iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | l1_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | sP1_iProver_split != iProver_top ),
% 2.20/1.02      inference(light_normalisation,[status(thm)],[c_2025,c_1314]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1322,plain,
% 2.20/1.02      ( ~ l1_pre_topc(sK3) | ~ v2_pre_topc(sK3) | sP1_iProver_split ),
% 2.20/1.02      inference(splitting,
% 2.20/1.02                [splitting(split),new_symbols(definition,[])],
% 2.20/1.02                [c_1293]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_1382,plain,
% 2.20/1.02      ( l1_pre_topc(sK3) != iProver_top
% 2.20/1.02      | v2_pre_topc(sK3) != iProver_top
% 2.20/1.02      | sP1_iProver_split = iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1322]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2811,plain,
% 2.20/1.02      ( v2_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | l1_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | v2_struct_0(X1_55) = iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.20/1.02      | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,sK3) != iProver_top
% 2.20/1.02      | r1_tarski(sK5,u1_struct_0(X1_55)) != iProver_top
% 2.20/1.02      | r1_tmap_1(sK3,X0_55,sK4,sK7) != iProver_top
% 2.20/1.02      | r1_tmap_1(X1_55,X0_55,k2_tmap_1(sK3,X0_55,sK4,X1_55),sK7) = iProver_top
% 2.20/1.02      | u1_struct_0(X0_55) != u1_struct_0(sK1) ),
% 2.20/1.02      inference(global_propositional_subsumption,
% 2.20/1.02                [status(thm)],
% 2.20/1.02                [c_2149,c_31,c_32,c_39,c_1382,c_2349,c_2363]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2812,plain,
% 2.20/1.02      ( u1_struct_0(X0_55) != u1_struct_0(sK1)
% 2.20/1.02      | r1_tmap_1(X1_55,X0_55,k2_tmap_1(sK3,X0_55,sK4,X1_55),sK7) = iProver_top
% 2.20/1.02      | r1_tmap_1(sK3,X0_55,sK4,sK7) != iProver_top
% 2.20/1.02      | r1_tarski(sK5,u1_struct_0(X1_55)) != iProver_top
% 2.20/1.02      | m1_pre_topc(X1_55,sK3) != iProver_top
% 2.20/1.02      | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X1_55) = iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | l1_pre_topc(X0_55) != iProver_top
% 2.20/1.02      | v2_pre_topc(X0_55) != iProver_top ),
% 2.20/1.02      inference(renaming,[status(thm)],[c_2811]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_2828,plain,
% 2.20/1.02      ( r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) = iProver_top
% 2.20/1.02      | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 2.20/1.02      | r1_tarski(sK5,u1_struct_0(X0_55)) != iProver_top
% 2.20/1.02      | m1_pre_topc(X0_55,sK3) != iProver_top
% 2.20/1.02      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 2.20/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.20/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.20/1.02      | v2_struct_0(sK1) = iProver_top
% 2.20/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.20/1.02      | v2_pre_topc(sK1) != iProver_top ),
% 2.20/1.02      inference(equality_resolution,[status(thm)],[c_2812]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_3134,plain,
% 2.20/1.02      ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top ),
% 2.20/1.02      inference(global_propositional_subsumption,
% 2.20/1.02                [status(thm)],
% 2.20/1.02                [c_2828,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,
% 2.20/1.02                 c_39,c_42,c_43,c_46,c_2055,c_2089,c_2496,c_2506,c_2994]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_12,negated_conjecture,
% 2.20/1.02      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 2.20/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(c_47,plain,
% 2.20/1.02      ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
% 2.20/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.20/1.02  
% 2.20/1.02  cnf(contradiction,plain,
% 2.20/1.02      ( $false ),
% 2.20/1.02      inference(minisat,
% 2.20/1.02                [status(thm)],
% 2.20/1.02                [c_3547,c_3357,c_3134,c_47,c_46,c_43,c_36]) ).
% 2.20/1.02  
% 2.20/1.02  
% 2.20/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.20/1.02  
% 2.20/1.02  ------                               Statistics
% 2.20/1.02  
% 2.20/1.02  ------ General
% 2.20/1.02  
% 2.20/1.02  abstr_ref_over_cycles:                  0
% 2.20/1.02  abstr_ref_under_cycles:                 0
% 2.20/1.02  gc_basic_clause_elim:                   0
% 2.20/1.02  forced_gc_time:                         0
% 2.20/1.02  parsing_time:                           0.013
% 2.20/1.02  unif_index_cands_time:                  0.
% 2.20/1.02  unif_index_add_time:                    0.
% 2.20/1.02  orderings_time:                         0.
% 2.20/1.02  out_proof_time:                         0.025
% 2.20/1.02  total_time:                             0.203
% 2.20/1.02  num_of_symbols:                         61
% 2.20/1.02  num_of_terms:                           2632
% 2.20/1.02  
% 2.20/1.02  ------ Preprocessing
% 2.20/1.02  
% 2.20/1.02  num_of_splits:                          2
% 2.20/1.02  num_of_split_atoms:                     2
% 2.20/1.02  num_of_reused_defs:                     0
% 2.20/1.02  num_eq_ax_congr_red:                    26
% 2.20/1.02  num_of_sem_filtered_clauses:            1
% 2.20/1.02  num_of_subtypes:                        3
% 2.20/1.02  monotx_restored_types:                  0
% 2.20/1.02  sat_num_of_epr_types:                   0
% 2.20/1.02  sat_num_of_non_cyclic_types:            0
% 2.20/1.02  sat_guarded_non_collapsed_types:        0
% 2.20/1.02  num_pure_diseq_elim:                    0
% 2.20/1.02  simp_replaced_by:                       0
% 2.20/1.02  res_preprocessed:                       142
% 2.20/1.02  prep_upred:                             0
% 2.20/1.02  prep_unflattend:                        12
% 2.20/1.02  smt_new_axioms:                         0
% 2.20/1.02  pred_elim_cands:                        7
% 2.20/1.02  pred_elim:                              3
% 2.20/1.02  pred_elim_cl:                           3
% 2.20/1.02  pred_elim_cycles:                       6
% 2.20/1.02  merged_defs:                            8
% 2.20/1.02  merged_defs_ncl:                        0
% 2.20/1.02  bin_hyper_res:                          8
% 2.20/1.02  prep_cycles:                            4
% 2.20/1.02  pred_elim_time:                         0.031
% 2.20/1.02  splitting_time:                         0.
% 2.20/1.02  sem_filter_time:                        0.
% 2.20/1.02  monotx_time:                            0.
% 2.20/1.02  subtype_inf_time:                       0.
% 2.20/1.02  
% 2.20/1.02  ------ Problem properties
% 2.20/1.02  
% 2.20/1.02  clauses:                                29
% 2.20/1.02  conjectures:                            19
% 2.20/1.02  epr:                                    16
% 2.20/1.02  horn:                                   23
% 2.20/1.02  ground:                                 21
% 2.20/1.02  unary:                                  17
% 2.20/1.02  binary:                                 3
% 2.20/1.02  lits:                                   102
% 2.20/1.02  lits_eq:                                12
% 2.20/1.02  fd_pure:                                0
% 2.20/1.02  fd_pseudo:                              0
% 2.20/1.02  fd_cond:                                0
% 2.20/1.02  fd_pseudo_cond:                         0
% 2.20/1.02  ac_symbols:                             0
% 2.20/1.02  
% 2.20/1.02  ------ Propositional Solver
% 2.20/1.02  
% 2.20/1.02  prop_solver_calls:                      28
% 2.20/1.02  prop_fast_solver_calls:                 1519
% 2.20/1.02  smt_solver_calls:                       0
% 2.20/1.02  smt_fast_solver_calls:                  0
% 2.20/1.02  prop_num_of_clauses:                    795
% 2.20/1.02  prop_preprocess_simplified:             3548
% 2.20/1.02  prop_fo_subsumed:                       59
% 2.20/1.02  prop_solver_time:                       0.
% 2.20/1.02  smt_solver_time:                        0.
% 2.20/1.02  smt_fast_solver_time:                   0.
% 2.20/1.02  prop_fast_solver_time:                  0.
% 2.20/1.02  prop_unsat_core_time:                   0.
% 2.20/1.02  
% 2.20/1.02  ------ QBF
% 2.20/1.02  
% 2.20/1.02  qbf_q_res:                              0
% 2.20/1.02  qbf_num_tautologies:                    0
% 2.20/1.02  qbf_prep_cycles:                        0
% 2.20/1.02  
% 2.20/1.02  ------ BMC1
% 2.20/1.02  
% 2.20/1.02  bmc1_current_bound:                     -1
% 2.20/1.02  bmc1_last_solved_bound:                 -1
% 2.20/1.02  bmc1_unsat_core_size:                   -1
% 2.20/1.02  bmc1_unsat_core_parents_size:           -1
% 2.20/1.02  bmc1_merge_next_fun:                    0
% 2.20/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.20/1.02  
% 2.20/1.02  ------ Instantiation
% 2.20/1.02  
% 2.20/1.02  inst_num_of_clauses:                    244
% 2.20/1.02  inst_num_in_passive:                    35
% 2.20/1.02  inst_num_in_active:                     187
% 2.20/1.02  inst_num_in_unprocessed:                22
% 2.20/1.02  inst_num_of_loops:                      220
% 2.20/1.02  inst_num_of_learning_restarts:          0
% 2.20/1.02  inst_num_moves_active_passive:          28
% 2.20/1.02  inst_lit_activity:                      0
% 2.20/1.02  inst_lit_activity_moves:                0
% 2.20/1.02  inst_num_tautologies:                   0
% 2.20/1.02  inst_num_prop_implied:                  0
% 2.20/1.02  inst_num_existing_simplified:           0
% 2.20/1.02  inst_num_eq_res_simplified:             0
% 2.20/1.02  inst_num_child_elim:                    0
% 2.20/1.02  inst_num_of_dismatching_blockings:      23
% 2.20/1.02  inst_num_of_non_proper_insts:           231
% 2.20/1.02  inst_num_of_duplicates:                 0
% 2.20/1.02  inst_inst_num_from_inst_to_res:         0
% 2.20/1.02  inst_dismatching_checking_time:         0.
% 2.20/1.02  
% 2.20/1.02  ------ Resolution
% 2.20/1.02  
% 2.20/1.02  res_num_of_clauses:                     0
% 2.20/1.02  res_num_in_passive:                     0
% 2.20/1.02  res_num_in_active:                      0
% 2.20/1.02  res_num_of_loops:                       146
% 2.20/1.02  res_forward_subset_subsumed:            50
% 2.20/1.02  res_backward_subset_subsumed:           0
% 2.20/1.02  res_forward_subsumed:                   0
% 2.20/1.02  res_backward_subsumed:                  0
% 2.20/1.02  res_forward_subsumption_resolution:     0
% 2.20/1.02  res_backward_subsumption_resolution:    0
% 2.20/1.02  res_clause_to_clause_subsumption:       209
% 2.20/1.02  res_orphan_elimination:                 0
% 2.20/1.02  res_tautology_del:                      60
% 2.20/1.02  res_num_eq_res_simplified:              0
% 2.20/1.02  res_num_sel_changes:                    0
% 2.20/1.02  res_moves_from_active_to_pass:          0
% 2.20/1.02  
% 2.20/1.02  ------ Superposition
% 2.20/1.02  
% 2.20/1.02  sup_time_total:                         0.
% 2.20/1.02  sup_time_generating:                    0.
% 2.20/1.02  sup_time_sim_full:                      0.
% 2.20/1.02  sup_time_sim_immed:                     0.
% 2.20/1.02  
% 2.20/1.02  sup_num_of_clauses:                     44
% 2.20/1.02  sup_num_in_active:                      41
% 2.20/1.02  sup_num_in_passive:                     3
% 2.20/1.02  sup_num_of_loops:                       43
% 2.20/1.02  sup_fw_superposition:                   9
% 2.20/1.02  sup_bw_superposition:                   3
% 2.20/1.02  sup_immediate_simplified:               2
% 2.20/1.02  sup_given_eliminated:                   0
% 2.20/1.02  comparisons_done:                       0
% 2.20/1.02  comparisons_avoided:                    0
% 2.20/1.02  
% 2.20/1.02  ------ Simplifications
% 2.20/1.02  
% 2.20/1.02  
% 2.20/1.02  sim_fw_subset_subsumed:                 0
% 2.20/1.02  sim_bw_subset_subsumed:                 2
% 2.20/1.02  sim_fw_subsumed:                        0
% 2.20/1.02  sim_bw_subsumed:                        0
% 2.20/1.02  sim_fw_subsumption_res:                 0
% 2.20/1.02  sim_bw_subsumption_res:                 0
% 2.20/1.02  sim_tautology_del:                      1
% 2.20/1.02  sim_eq_tautology_del:                   0
% 2.20/1.02  sim_eq_res_simp:                        0
% 2.20/1.02  sim_fw_demodulated:                     2
% 2.20/1.02  sim_bw_demodulated:                     1
% 2.20/1.02  sim_light_normalised:                   5
% 2.20/1.02  sim_joinable_taut:                      0
% 2.20/1.02  sim_joinable_simp:                      0
% 2.20/1.02  sim_ac_normalised:                      0
% 2.20/1.02  sim_smt_subsumption:                    0
% 2.20/1.02  
%------------------------------------------------------------------------------
