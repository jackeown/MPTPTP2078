%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:10 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  200 (1506 expanded)
%              Number of clauses        :  136 ( 259 expanded)
%              Number of leaves         :   16 ( 690 expanded)
%              Depth                    :   33
%              Number of atoms          : 1723 (33820 expanded)
%              Number of equality atoms :  412 (2241 expanded)
%              Maximal formula depth    :   28 (   9 average)
%              Maximal clause size      :   50 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
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
                                          & r1_tarski(X5,u1_struct_0(X2))
                                          & r2_hidden(X6,X5)
                                          & v3_pre_topc(X5,X3) )
                                       => ( r1_tmap_1(X3,X1,X4,X6)
                                        <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
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
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
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
    inference(flattening,[],[f20])).

fof(f23,plain,(
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
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
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
    inference(nnf_transformation,[],[f21])).

fof(f24,plain,(
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
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
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

fof(f32,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
            | ~ r1_tmap_1(X3,X1,X4,X6) )
          & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
            | r1_tmap_1(X3,X1,X4,X6) )
          & X6 = X7
          & r1_tarski(X5,u1_struct_0(X2))
          & r2_hidden(X6,X5)
          & v3_pre_topc(X5,X3)
          & m1_subset_1(X7,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7)
          | ~ r1_tmap_1(X3,X1,X4,X6) )
        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7)
          | r1_tmap_1(X3,X1,X4,X6) )
        & sK7 = X6
        & r1_tarski(X5,u1_struct_0(X2))
        & r2_hidden(X6,X5)
        & v3_pre_topc(X5,X3)
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                | ~ r1_tmap_1(X3,X1,X4,X6) )
              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                | r1_tmap_1(X3,X1,X4,X6) )
              & X6 = X7
              & r1_tarski(X5,u1_struct_0(X2))
              & r2_hidden(X6,X5)
              & v3_pre_topc(X5,X3)
              & m1_subset_1(X7,u1_struct_0(X2)) )
          & m1_subset_1(X6,u1_struct_0(X3)) )
     => ( ? [X7] :
            ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
              | ~ r1_tmap_1(X3,X1,X4,sK6) )
            & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
              | r1_tmap_1(X3,X1,X4,sK6) )
            & sK6 = X7
            & r1_tarski(X5,u1_struct_0(X2))
            & r2_hidden(sK6,X5)
            & v3_pre_topc(X5,X3)
            & m1_subset_1(X7,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                  & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                    | r1_tmap_1(X3,X1,X4,X6) )
                  & X6 = X7
                  & r1_tarski(X5,u1_struct_0(X2))
                  & r2_hidden(X6,X5)
                  & v3_pre_topc(X5,X3)
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
                & r1_tarski(sK5,u1_struct_0(X2))
                & r2_hidden(X6,sK5)
                & v3_pre_topc(sK5,X3)
                & m1_subset_1(X7,u1_struct_0(X2)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
                      & r1_tarski(X5,u1_struct_0(X2))
                      & r2_hidden(X6,X5)
                      & v3_pre_topc(X5,X3)
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
                    & r1_tarski(X5,u1_struct_0(X2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,X3)
                    & m1_subset_1(X7,u1_struct_0(X2)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
                          & r1_tarski(X5,u1_struct_0(X2))
                          & r2_hidden(X6,X5)
                          & v3_pre_topc(X5,X3)
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
                        & r1_tarski(X5,u1_struct_0(X2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,sK3)
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

fof(f27,plain,(
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
                              & r1_tarski(X5,u1_struct_0(X2))
                              & r2_hidden(X6,X5)
                              & v3_pre_topc(X5,X3)
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
                            & r1_tarski(X5,u1_struct_0(sK2))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,X3)
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

fof(f26,plain,(
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
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
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
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,X3)
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

fof(f25,plain,
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
                                    & r1_tarski(X5,u1_struct_0(X2))
                                    & r2_hidden(X6,X5)
                                    & v3_pre_topc(X5,X3)
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
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
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

fof(f33,plain,
    ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
      | ~ r1_tmap_1(sK3,sK1,sK4,sK6) )
    & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
      | r1_tmap_1(sK3,sK1,sK4,sK6) )
    & sK6 = sK7
    & r1_tarski(sK5,u1_struct_0(sK2))
    & r2_hidden(sK6,sK5)
    & v3_pre_topc(sK5,sK3)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f24,f32,f31,f30,f29,f28,f27,f26,f25])).

fof(f48,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f37,plain,(
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
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f36,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f33])).

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

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
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
    inference(equality_resolution,[],[f40])).

fof(f58,plain,(
    v3_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f33])).

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
                                  & r1_tarski(X4,u1_struct_0(X3))
                                  & r2_hidden(X5,X4)
                                  & v3_pre_topc(X4,X1) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
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
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
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
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
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
    inference(flattening,[],[f16])).

fof(f22,plain,(
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
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
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
    inference(nnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | X5 != X6
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X5,X4)
      | ~ v3_pre_topc(X4,X1)
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
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X6,X4)
      | ~ v3_pre_topc(X4,X1)
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
    inference(equality_resolution,[],[f39])).

fof(f60,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1236,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1879,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1236])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_727,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_18])).

cnf(c_728,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_727])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_732,plain,
    ( v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_728,c_19])).

cnf(c_733,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_732])).

cnf(c_1228,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ m1_pre_topc(X2_53,X3_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_pre_topc(X2_53,X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X3_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X3_53)
    | u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK4,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4) ),
    inference(subtyping,[status(esa)],[c_733])).

cnf(c_1887,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK4,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X2_53,X3_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1228])).

cnf(c_2954,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X1_53,X2_53) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1887])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_33,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_34,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_35,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2172,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_pre_topc(X2_53,X0_53)
    | ~ m1_pre_topc(X2_53,X1_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X2_53)) = k3_tmap_1(X1_53,sK1,X0_53,X2_53,sK4) ),
    inference(instantiation,[status(thm)],[c_1228])).

cnf(c_2173,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X1_53,X2_53) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2172])).

cnf(c_1255,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_2320,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1255])).

cnf(c_3111,plain,
    ( v2_pre_topc(X2_53) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | m1_pre_topc(X1_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4)
    | u1_struct_0(X0_53) != u1_struct_0(sK3)
    | l1_pre_topc(X2_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2954,c_33,c_34,c_35,c_2173,c_2320])).

cnf(c_3112,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X1_53,X2_53) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_3111])).

cnf(c_3126,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3112])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3322,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4)
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3126,c_42])).

cnf(c_3337,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1879,c_3322])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1240,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1875,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1240])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_778,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_779,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_778])).

cnf(c_783,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_779,c_19])).

cnf(c_784,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_783])).

cnf(c_1227,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ m1_pre_topc(X2_53,X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X0_53)
    | u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK4,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,sK4,X2_53) ),
    inference(subtyping,[status(esa)],[c_784])).

cnf(c_1888,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK4,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,sK4,X2_53)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1227])).

cnf(c_2936,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k2_tmap_1(X0_53,sK1,sK4,X1_53)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1888])).

cnf(c_2162,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X1_53,X0_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k2_tmap_1(X0_53,sK1,sK4,X1_53) ),
    inference(instantiation,[status(thm)],[c_1227])).

cnf(c_2163,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k2_tmap_1(X0_53,sK1,sK4,X1_53)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2162])).

cnf(c_3036,plain,
    ( v2_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k2_tmap_1(X0_53,sK1,sK4,X1_53)
    | u1_struct_0(X0_53) != u1_struct_0(sK3)
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2936,c_33,c_34,c_35,c_2163,c_2320])).

cnf(c_3037,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k2_tmap_1(X0_53,sK1,sK4,X1_53)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_3036])).

cnf(c_3049,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK3,sK1,sK4,X0_53)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3037])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_31,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_32,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_38,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_39,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1247,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2197,plain,
    ( ~ m1_pre_topc(X0_53,sK0)
    | l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1247])).

cnf(c_2198,plain,
    ( m1_pre_topc(X0_53,sK0) != iProver_top
    | l1_pre_topc(X0_53) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2197])).

cnf(c_2200,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2198])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1248,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v2_pre_topc(X1_53)
    | v2_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2207,plain,
    ( ~ m1_pre_topc(X0_53,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1248])).

cnf(c_2208,plain,
    ( m1_pre_topc(X0_53,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(X0_53) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2207])).

cnf(c_2210,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2208])).

cnf(c_3263,plain,
    ( m1_pre_topc(X0_53,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK3,sK1,sK4,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3049,c_31,c_32,c_38,c_39,c_42,c_2200,c_2210])).

cnf(c_3264,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK3,sK1,sK4,X0_53)
    | m1_pre_topc(X0_53,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3263])).

cnf(c_3271,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_1875,c_3264])).

cnf(c_3344,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3337,c_3271])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_30,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_43,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3434,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3344,c_30,c_31,c_32,c_39,c_43])).

cnf(c_8,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1245,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1871,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1245])).

cnf(c_9,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1244,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1945,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1871,c_1244])).

cnf(c_3437,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3434,c_1945])).

cnf(c_6,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_823,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_824,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_823])).

cnf(c_828,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_824,c_19])).

cnf(c_829,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_828])).

cnf(c_1226,plain,
    ( r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),X0_54)
    | ~ r1_tmap_1(X3_53,X1_53,sK4,X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(X3_53))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
    | ~ m1_pre_topc(X3_53,X2_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_pre_topc(X0_53,X2_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X3_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_829])).

cnf(c_2182,plain,
    ( r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,X2_53,X0_53,sK4),X0_54)
    | ~ r1_tmap_1(X2_53,sK1,sK4,X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(X2_53))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_pre_topc(X2_53,X1_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X2_53) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1226])).

cnf(c_2410,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,X0_54)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(X0_53,sK1,sK3,sK2,sK4),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,X0_53)
    | ~ m1_pre_topc(sK2,X0_53)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2182])).

cnf(c_2794,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,X0_54)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2410])).

cnf(c_3304,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK7)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2794])).

cnf(c_3307,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3304])).

cnf(c_12,negated_conjecture,
    ( v3_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_11,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_4,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X5,X0)
    | ~ r2_hidden(X3,X5)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_430,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X5,X0)
    | ~ r2_hidden(X3,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X4) != u1_struct_0(sK2)
    | sK5 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_431,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(sK5,X0)
    | ~ r2_hidden(X3,sK5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X4,X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X4) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_495,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X4,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X4) != u1_struct_0(sK2)
    | sK5 != sK5
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_431])).

cnf(c_496,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_671,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X3) != u1_struct_0(sK2)
    | sK5 != sK5
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_496])).

cnf(c_672,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
    | r1_tmap_1(sK3,X1,X2,sK6)
    | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_671])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_676,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
    | r1_tmap_1(sK3,X1,X2,sK6)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_672,c_21,c_15,c_14])).

cnf(c_677,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
    | r1_tmap_1(sK3,X1,X2,sK6)
    | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_676])).

cnf(c_889,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
    | r1_tmap_1(sK3,X1,X2,sK6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_677])).

cnf(c_890,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
    | r1_tmap_1(sK3,X1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_894,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | r1_tmap_1(sK3,X1,sK4,sK6)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_890,c_19])).

cnf(c_895,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
    | r1_tmap_1(sK3,X1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_894])).

cnf(c_1225,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK3,X1_53,sK4,X0_53),sK6)
    | r1_tmap_1(sK3,X1_53,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
    | ~ m1_pre_topc(X0_53,sK3)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | u1_struct_0(X0_53) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_895])).

cnf(c_1249,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK3,X1_53,sK4,X0_53),sK6)
    | r1_tmap_1(sK3,X1_53,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
    | ~ m1_pre_topc(X0_53,sK3)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v2_pre_topc(X1_53)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | u1_struct_0(X0_53) != u1_struct_0(sK2)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1225])).

cnf(c_1891,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(X1_53) != u1_struct_0(sK2)
    | r1_tmap_1(X1_53,X0_53,k2_tmap_1(sK3,X0_53,sK4,X1_53),sK6) != iProver_top
    | r1_tmap_1(sK3,X0_53,sK4,sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53)))) != iProver_top
    | m1_pre_topc(X1_53,sK3) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1249])).

cnf(c_1985,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(X1_53) != u1_struct_0(sK2)
    | r1_tmap_1(X1_53,X0_53,k2_tmap_1(sK3,X0_53,sK4,X1_53),sK7) != iProver_top
    | r1_tmap_1(sK3,X0_53,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53)))) != iProver_top
    | m1_pre_topc(X1_53,sK3) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1891,c_1244])).

cnf(c_1250,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1225])).

cnf(c_1303,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1250])).

cnf(c_2527,plain,
    ( v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | m1_pre_topc(X1_53,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
    | r1_tmap_1(sK3,X0_53,sK4,sK7) = iProver_top
    | r1_tmap_1(X1_53,X0_53,k2_tmap_1(sK3,X0_53,sK4,X1_53),sK7) != iProver_top
    | u1_struct_0(X1_53) != u1_struct_0(sK2)
    | u1_struct_0(X0_53) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1985,c_31,c_32,c_39,c_1303,c_2200,c_2210])).

cnf(c_2528,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(X1_53) != u1_struct_0(sK2)
    | r1_tmap_1(X1_53,X0_53,k2_tmap_1(sK3,X0_53,sK4,X1_53),sK7) != iProver_top
    | r1_tmap_1(sK3,X0_53,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53)))) != iProver_top
    | m1_pre_topc(X1_53,sK3) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2527])).

cnf(c_2544,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK2)
    | r1_tmap_1(X0_53,sK1,k2_tmap_1(sK3,sK1,sK4,X0_53),sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2528])).

cnf(c_2854,plain,
    ( v2_struct_0(X0_53) = iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | u1_struct_0(X0_53) != u1_struct_0(sK2)
    | r1_tmap_1(X0_53,sK1,k2_tmap_1(sK3,sK1,sK4,X0_53),sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2544,c_33,c_34,c_35,c_42])).

cnf(c_2855,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK2)
    | r1_tmap_1(X0_53,sK1,k2_tmap_1(sK3,sK1,sK4,X0_53),sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | v2_struct_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_2854])).

cnf(c_2866,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2855])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_36,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_46,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3216,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2866,c_36,c_43,c_46])).

cnf(c_3217,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_3216])).

cnf(c_2338,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1255])).

cnf(c_1242,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1873,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1242])).

cnf(c_1920,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1873,c_1244])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1246,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1870,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1246])).

cnf(c_1950,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1870,c_1244])).

cnf(c_37,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3437,c_3307,c_3217,c_2338,c_2320,c_1920,c_1950,c_46,c_43,c_42,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.10/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.00  
% 2.10/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.10/1.00  
% 2.10/1.00  ------  iProver source info
% 2.10/1.00  
% 2.10/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.10/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.10/1.00  git: non_committed_changes: false
% 2.10/1.00  git: last_make_outside_of_git: false
% 2.10/1.00  
% 2.10/1.00  ------ 
% 2.10/1.00  
% 2.10/1.00  ------ Input Options
% 2.10/1.00  
% 2.10/1.00  --out_options                           all
% 2.10/1.00  --tptp_safe_out                         true
% 2.10/1.00  --problem_path                          ""
% 2.10/1.00  --include_path                          ""
% 2.10/1.00  --clausifier                            res/vclausify_rel
% 2.10/1.00  --clausifier_options                    --mode clausify
% 2.10/1.00  --stdin                                 false
% 2.10/1.00  --stats_out                             all
% 2.10/1.00  
% 2.10/1.00  ------ General Options
% 2.10/1.00  
% 2.10/1.00  --fof                                   false
% 2.10/1.00  --time_out_real                         305.
% 2.10/1.00  --time_out_virtual                      -1.
% 2.10/1.00  --symbol_type_check                     false
% 2.10/1.00  --clausify_out                          false
% 2.10/1.00  --sig_cnt_out                           false
% 2.10/1.00  --trig_cnt_out                          false
% 2.10/1.00  --trig_cnt_out_tolerance                1.
% 2.10/1.00  --trig_cnt_out_sk_spl                   false
% 2.10/1.00  --abstr_cl_out                          false
% 2.10/1.00  
% 2.10/1.00  ------ Global Options
% 2.10/1.00  
% 2.10/1.00  --schedule                              default
% 2.10/1.00  --add_important_lit                     false
% 2.10/1.00  --prop_solver_per_cl                    1000
% 2.10/1.00  --min_unsat_core                        false
% 2.10/1.00  --soft_assumptions                      false
% 2.10/1.00  --soft_lemma_size                       3
% 2.10/1.00  --prop_impl_unit_size                   0
% 2.10/1.00  --prop_impl_unit                        []
% 2.10/1.00  --share_sel_clauses                     true
% 2.10/1.00  --reset_solvers                         false
% 2.10/1.00  --bc_imp_inh                            [conj_cone]
% 2.10/1.00  --conj_cone_tolerance                   3.
% 2.10/1.00  --extra_neg_conj                        none
% 2.10/1.00  --large_theory_mode                     true
% 2.10/1.00  --prolific_symb_bound                   200
% 2.10/1.00  --lt_threshold                          2000
% 2.10/1.00  --clause_weak_htbl                      true
% 2.10/1.00  --gc_record_bc_elim                     false
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing Options
% 2.10/1.00  
% 2.10/1.00  --preprocessing_flag                    true
% 2.10/1.00  --time_out_prep_mult                    0.1
% 2.10/1.00  --splitting_mode                        input
% 2.10/1.00  --splitting_grd                         true
% 2.10/1.00  --splitting_cvd                         false
% 2.10/1.00  --splitting_cvd_svl                     false
% 2.10/1.00  --splitting_nvd                         32
% 2.10/1.00  --sub_typing                            true
% 2.10/1.00  --prep_gs_sim                           true
% 2.10/1.00  --prep_unflatten                        true
% 2.10/1.00  --prep_res_sim                          true
% 2.10/1.00  --prep_upred                            true
% 2.10/1.00  --prep_sem_filter                       exhaustive
% 2.10/1.00  --prep_sem_filter_out                   false
% 2.10/1.00  --pred_elim                             true
% 2.10/1.00  --res_sim_input                         true
% 2.10/1.00  --eq_ax_congr_red                       true
% 2.10/1.00  --pure_diseq_elim                       true
% 2.10/1.00  --brand_transform                       false
% 2.10/1.00  --non_eq_to_eq                          false
% 2.10/1.00  --prep_def_merge                        true
% 2.10/1.00  --prep_def_merge_prop_impl              false
% 2.10/1.00  --prep_def_merge_mbd                    true
% 2.10/1.00  --prep_def_merge_tr_red                 false
% 2.10/1.00  --prep_def_merge_tr_cl                  false
% 2.10/1.00  --smt_preprocessing                     true
% 2.10/1.00  --smt_ac_axioms                         fast
% 2.10/1.00  --preprocessed_out                      false
% 2.10/1.00  --preprocessed_stats                    false
% 2.10/1.00  
% 2.10/1.00  ------ Abstraction refinement Options
% 2.10/1.00  
% 2.10/1.00  --abstr_ref                             []
% 2.10/1.00  --abstr_ref_prep                        false
% 2.10/1.00  --abstr_ref_until_sat                   false
% 2.10/1.00  --abstr_ref_sig_restrict                funpre
% 2.10/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.10/1.00  --abstr_ref_under                       []
% 2.10/1.00  
% 2.10/1.00  ------ SAT Options
% 2.10/1.00  
% 2.10/1.00  --sat_mode                              false
% 2.10/1.00  --sat_fm_restart_options                ""
% 2.10/1.00  --sat_gr_def                            false
% 2.10/1.00  --sat_epr_types                         true
% 2.10/1.00  --sat_non_cyclic_types                  false
% 2.10/1.00  --sat_finite_models                     false
% 2.10/1.00  --sat_fm_lemmas                         false
% 2.10/1.00  --sat_fm_prep                           false
% 2.10/1.00  --sat_fm_uc_incr                        true
% 2.10/1.00  --sat_out_model                         small
% 2.10/1.00  --sat_out_clauses                       false
% 2.10/1.00  
% 2.10/1.00  ------ QBF Options
% 2.10/1.00  
% 2.10/1.00  --qbf_mode                              false
% 2.10/1.00  --qbf_elim_univ                         false
% 2.10/1.00  --qbf_dom_inst                          none
% 2.10/1.00  --qbf_dom_pre_inst                      false
% 2.10/1.00  --qbf_sk_in                             false
% 2.10/1.00  --qbf_pred_elim                         true
% 2.10/1.00  --qbf_split                             512
% 2.10/1.00  
% 2.10/1.00  ------ BMC1 Options
% 2.10/1.00  
% 2.10/1.00  --bmc1_incremental                      false
% 2.10/1.00  --bmc1_axioms                           reachable_all
% 2.10/1.00  --bmc1_min_bound                        0
% 2.10/1.00  --bmc1_max_bound                        -1
% 2.10/1.00  --bmc1_max_bound_default                -1
% 2.10/1.00  --bmc1_symbol_reachability              true
% 2.10/1.00  --bmc1_property_lemmas                  false
% 2.10/1.00  --bmc1_k_induction                      false
% 2.10/1.00  --bmc1_non_equiv_states                 false
% 2.10/1.00  --bmc1_deadlock                         false
% 2.10/1.00  --bmc1_ucm                              false
% 2.10/1.00  --bmc1_add_unsat_core                   none
% 2.10/1.00  --bmc1_unsat_core_children              false
% 2.10/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.10/1.00  --bmc1_out_stat                         full
% 2.10/1.00  --bmc1_ground_init                      false
% 2.10/1.00  --bmc1_pre_inst_next_state              false
% 2.10/1.00  --bmc1_pre_inst_state                   false
% 2.10/1.00  --bmc1_pre_inst_reach_state             false
% 2.10/1.00  --bmc1_out_unsat_core                   false
% 2.10/1.00  --bmc1_aig_witness_out                  false
% 2.10/1.00  --bmc1_verbose                          false
% 2.10/1.00  --bmc1_dump_clauses_tptp                false
% 2.10/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.10/1.00  --bmc1_dump_file                        -
% 2.10/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.10/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.10/1.00  --bmc1_ucm_extend_mode                  1
% 2.10/1.00  --bmc1_ucm_init_mode                    2
% 2.10/1.00  --bmc1_ucm_cone_mode                    none
% 2.10/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.10/1.00  --bmc1_ucm_relax_model                  4
% 2.10/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.10/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.10/1.00  --bmc1_ucm_layered_model                none
% 2.10/1.00  --bmc1_ucm_max_lemma_size               10
% 2.10/1.00  
% 2.10/1.00  ------ AIG Options
% 2.10/1.00  
% 2.10/1.00  --aig_mode                              false
% 2.10/1.00  
% 2.10/1.00  ------ Instantiation Options
% 2.10/1.00  
% 2.10/1.00  --instantiation_flag                    true
% 2.10/1.00  --inst_sos_flag                         false
% 2.10/1.00  --inst_sos_phase                        true
% 2.10/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.10/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.10/1.00  --inst_lit_sel_side                     num_symb
% 2.10/1.00  --inst_solver_per_active                1400
% 2.10/1.00  --inst_solver_calls_frac                1.
% 2.10/1.00  --inst_passive_queue_type               priority_queues
% 2.10/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.10/1.00  --inst_passive_queues_freq              [25;2]
% 2.10/1.00  --inst_dismatching                      true
% 2.10/1.00  --inst_eager_unprocessed_to_passive     true
% 2.10/1.00  --inst_prop_sim_given                   true
% 2.10/1.00  --inst_prop_sim_new                     false
% 2.10/1.00  --inst_subs_new                         false
% 2.10/1.00  --inst_eq_res_simp                      false
% 2.10/1.00  --inst_subs_given                       false
% 2.10/1.00  --inst_orphan_elimination               true
% 2.10/1.00  --inst_learning_loop_flag               true
% 2.10/1.00  --inst_learning_start                   3000
% 2.10/1.00  --inst_learning_factor                  2
% 2.10/1.00  --inst_start_prop_sim_after_learn       3
% 2.10/1.00  --inst_sel_renew                        solver
% 2.10/1.00  --inst_lit_activity_flag                true
% 2.10/1.00  --inst_restr_to_given                   false
% 2.10/1.00  --inst_activity_threshold               500
% 2.10/1.00  --inst_out_proof                        true
% 2.10/1.00  
% 2.10/1.00  ------ Resolution Options
% 2.10/1.00  
% 2.10/1.00  --resolution_flag                       true
% 2.10/1.00  --res_lit_sel                           adaptive
% 2.10/1.00  --res_lit_sel_side                      none
% 2.10/1.00  --res_ordering                          kbo
% 2.10/1.00  --res_to_prop_solver                    active
% 2.10/1.00  --res_prop_simpl_new                    false
% 2.10/1.00  --res_prop_simpl_given                  true
% 2.10/1.00  --res_passive_queue_type                priority_queues
% 2.10/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.10/1.00  --res_passive_queues_freq               [15;5]
% 2.10/1.00  --res_forward_subs                      full
% 2.10/1.00  --res_backward_subs                     full
% 2.10/1.00  --res_forward_subs_resolution           true
% 2.10/1.00  --res_backward_subs_resolution          true
% 2.10/1.00  --res_orphan_elimination                true
% 2.10/1.00  --res_time_limit                        2.
% 2.10/1.00  --res_out_proof                         true
% 2.10/1.00  
% 2.10/1.00  ------ Superposition Options
% 2.10/1.00  
% 2.10/1.00  --superposition_flag                    true
% 2.10/1.00  --sup_passive_queue_type                priority_queues
% 2.10/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.10/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.10/1.00  --demod_completeness_check              fast
% 2.10/1.00  --demod_use_ground                      true
% 2.10/1.00  --sup_to_prop_solver                    passive
% 2.10/1.00  --sup_prop_simpl_new                    true
% 2.10/1.00  --sup_prop_simpl_given                  true
% 2.10/1.00  --sup_fun_splitting                     false
% 2.10/1.00  --sup_smt_interval                      50000
% 2.10/1.00  
% 2.10/1.00  ------ Superposition Simplification Setup
% 2.10/1.00  
% 2.10/1.00  --sup_indices_passive                   []
% 2.10/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.10/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_full_bw                           [BwDemod]
% 2.10/1.00  --sup_immed_triv                        [TrivRules]
% 2.10/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.10/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_immed_bw_main                     []
% 2.10/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.10/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.00  
% 2.10/1.00  ------ Combination Options
% 2.10/1.00  
% 2.10/1.00  --comb_res_mult                         3
% 2.10/1.00  --comb_sup_mult                         2
% 2.10/1.00  --comb_inst_mult                        10
% 2.10/1.00  
% 2.10/1.00  ------ Debug Options
% 2.10/1.00  
% 2.10/1.00  --dbg_backtrace                         false
% 2.10/1.00  --dbg_dump_prop_clauses                 false
% 2.10/1.00  --dbg_dump_prop_clauses_file            -
% 2.10/1.00  --dbg_out_stat                          false
% 2.10/1.00  ------ Parsing...
% 2.10/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.10/1.00  ------ Proving...
% 2.10/1.00  ------ Problem Properties 
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  clauses                                 27
% 2.10/1.00  conjectures                             18
% 2.10/1.00  EPR                                     16
% 2.10/1.00  Horn                                    21
% 2.10/1.00  unary                                   16
% 2.10/1.00  binary                                  2
% 2.10/1.00  lits                                    99
% 2.10/1.00  lits eq                                 13
% 2.10/1.00  fd_pure                                 0
% 2.10/1.00  fd_pseudo                               0
% 2.10/1.00  fd_cond                                 0
% 2.10/1.00  fd_pseudo_cond                          0
% 2.10/1.00  AC symbols                              0
% 2.10/1.00  
% 2.10/1.00  ------ Schedule dynamic 5 is on 
% 2.10/1.00  
% 2.10/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  ------ 
% 2.10/1.00  Current options:
% 2.10/1.00  ------ 
% 2.10/1.00  
% 2.10/1.00  ------ Input Options
% 2.10/1.00  
% 2.10/1.00  --out_options                           all
% 2.10/1.00  --tptp_safe_out                         true
% 2.10/1.00  --problem_path                          ""
% 2.10/1.00  --include_path                          ""
% 2.10/1.00  --clausifier                            res/vclausify_rel
% 2.10/1.00  --clausifier_options                    --mode clausify
% 2.10/1.00  --stdin                                 false
% 2.10/1.00  --stats_out                             all
% 2.10/1.00  
% 2.10/1.00  ------ General Options
% 2.10/1.00  
% 2.10/1.00  --fof                                   false
% 2.10/1.00  --time_out_real                         305.
% 2.10/1.00  --time_out_virtual                      -1.
% 2.10/1.00  --symbol_type_check                     false
% 2.10/1.00  --clausify_out                          false
% 2.10/1.00  --sig_cnt_out                           false
% 2.10/1.00  --trig_cnt_out                          false
% 2.10/1.00  --trig_cnt_out_tolerance                1.
% 2.10/1.00  --trig_cnt_out_sk_spl                   false
% 2.10/1.00  --abstr_cl_out                          false
% 2.10/1.00  
% 2.10/1.00  ------ Global Options
% 2.10/1.00  
% 2.10/1.00  --schedule                              default
% 2.10/1.00  --add_important_lit                     false
% 2.10/1.00  --prop_solver_per_cl                    1000
% 2.10/1.00  --min_unsat_core                        false
% 2.10/1.00  --soft_assumptions                      false
% 2.10/1.00  --soft_lemma_size                       3
% 2.10/1.00  --prop_impl_unit_size                   0
% 2.10/1.00  --prop_impl_unit                        []
% 2.10/1.00  --share_sel_clauses                     true
% 2.10/1.00  --reset_solvers                         false
% 2.10/1.00  --bc_imp_inh                            [conj_cone]
% 2.10/1.00  --conj_cone_tolerance                   3.
% 2.10/1.00  --extra_neg_conj                        none
% 2.10/1.00  --large_theory_mode                     true
% 2.10/1.00  --prolific_symb_bound                   200
% 2.10/1.00  --lt_threshold                          2000
% 2.10/1.00  --clause_weak_htbl                      true
% 2.10/1.00  --gc_record_bc_elim                     false
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing Options
% 2.10/1.00  
% 2.10/1.00  --preprocessing_flag                    true
% 2.10/1.00  --time_out_prep_mult                    0.1
% 2.10/1.00  --splitting_mode                        input
% 2.10/1.00  --splitting_grd                         true
% 2.10/1.00  --splitting_cvd                         false
% 2.10/1.00  --splitting_cvd_svl                     false
% 2.10/1.00  --splitting_nvd                         32
% 2.10/1.00  --sub_typing                            true
% 2.10/1.00  --prep_gs_sim                           true
% 2.10/1.00  --prep_unflatten                        true
% 2.10/1.00  --prep_res_sim                          true
% 2.10/1.00  --prep_upred                            true
% 2.10/1.00  --prep_sem_filter                       exhaustive
% 2.10/1.00  --prep_sem_filter_out                   false
% 2.10/1.00  --pred_elim                             true
% 2.10/1.00  --res_sim_input                         true
% 2.10/1.00  --eq_ax_congr_red                       true
% 2.10/1.00  --pure_diseq_elim                       true
% 2.10/1.00  --brand_transform                       false
% 2.10/1.00  --non_eq_to_eq                          false
% 2.10/1.00  --prep_def_merge                        true
% 2.10/1.00  --prep_def_merge_prop_impl              false
% 2.10/1.00  --prep_def_merge_mbd                    true
% 2.10/1.00  --prep_def_merge_tr_red                 false
% 2.10/1.00  --prep_def_merge_tr_cl                  false
% 2.10/1.00  --smt_preprocessing                     true
% 2.10/1.00  --smt_ac_axioms                         fast
% 2.10/1.00  --preprocessed_out                      false
% 2.10/1.00  --preprocessed_stats                    false
% 2.10/1.00  
% 2.10/1.00  ------ Abstraction refinement Options
% 2.10/1.00  
% 2.10/1.00  --abstr_ref                             []
% 2.10/1.00  --abstr_ref_prep                        false
% 2.10/1.00  --abstr_ref_until_sat                   false
% 2.10/1.00  --abstr_ref_sig_restrict                funpre
% 2.10/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.10/1.00  --abstr_ref_under                       []
% 2.10/1.00  
% 2.10/1.00  ------ SAT Options
% 2.10/1.00  
% 2.10/1.00  --sat_mode                              false
% 2.10/1.00  --sat_fm_restart_options                ""
% 2.10/1.00  --sat_gr_def                            false
% 2.10/1.00  --sat_epr_types                         true
% 2.10/1.00  --sat_non_cyclic_types                  false
% 2.10/1.00  --sat_finite_models                     false
% 2.10/1.00  --sat_fm_lemmas                         false
% 2.10/1.00  --sat_fm_prep                           false
% 2.10/1.00  --sat_fm_uc_incr                        true
% 2.10/1.00  --sat_out_model                         small
% 2.10/1.00  --sat_out_clauses                       false
% 2.10/1.00  
% 2.10/1.00  ------ QBF Options
% 2.10/1.00  
% 2.10/1.00  --qbf_mode                              false
% 2.10/1.00  --qbf_elim_univ                         false
% 2.10/1.00  --qbf_dom_inst                          none
% 2.10/1.00  --qbf_dom_pre_inst                      false
% 2.10/1.00  --qbf_sk_in                             false
% 2.10/1.00  --qbf_pred_elim                         true
% 2.10/1.00  --qbf_split                             512
% 2.10/1.00  
% 2.10/1.00  ------ BMC1 Options
% 2.10/1.00  
% 2.10/1.00  --bmc1_incremental                      false
% 2.10/1.00  --bmc1_axioms                           reachable_all
% 2.10/1.00  --bmc1_min_bound                        0
% 2.10/1.00  --bmc1_max_bound                        -1
% 2.10/1.00  --bmc1_max_bound_default                -1
% 2.10/1.00  --bmc1_symbol_reachability              true
% 2.10/1.00  --bmc1_property_lemmas                  false
% 2.10/1.00  --bmc1_k_induction                      false
% 2.10/1.00  --bmc1_non_equiv_states                 false
% 2.10/1.00  --bmc1_deadlock                         false
% 2.10/1.00  --bmc1_ucm                              false
% 2.10/1.00  --bmc1_add_unsat_core                   none
% 2.10/1.00  --bmc1_unsat_core_children              false
% 2.10/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.10/1.00  --bmc1_out_stat                         full
% 2.10/1.00  --bmc1_ground_init                      false
% 2.10/1.00  --bmc1_pre_inst_next_state              false
% 2.10/1.00  --bmc1_pre_inst_state                   false
% 2.10/1.00  --bmc1_pre_inst_reach_state             false
% 2.10/1.00  --bmc1_out_unsat_core                   false
% 2.10/1.00  --bmc1_aig_witness_out                  false
% 2.10/1.00  --bmc1_verbose                          false
% 2.10/1.00  --bmc1_dump_clauses_tptp                false
% 2.10/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.10/1.00  --bmc1_dump_file                        -
% 2.10/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.10/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.10/1.00  --bmc1_ucm_extend_mode                  1
% 2.10/1.00  --bmc1_ucm_init_mode                    2
% 2.10/1.00  --bmc1_ucm_cone_mode                    none
% 2.10/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.10/1.00  --bmc1_ucm_relax_model                  4
% 2.10/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.10/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.10/1.00  --bmc1_ucm_layered_model                none
% 2.10/1.00  --bmc1_ucm_max_lemma_size               10
% 2.10/1.00  
% 2.10/1.00  ------ AIG Options
% 2.10/1.00  
% 2.10/1.00  --aig_mode                              false
% 2.10/1.00  
% 2.10/1.00  ------ Instantiation Options
% 2.10/1.00  
% 2.10/1.00  --instantiation_flag                    true
% 2.10/1.00  --inst_sos_flag                         false
% 2.10/1.00  --inst_sos_phase                        true
% 2.10/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.10/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.10/1.00  --inst_lit_sel_side                     none
% 2.10/1.00  --inst_solver_per_active                1400
% 2.10/1.00  --inst_solver_calls_frac                1.
% 2.10/1.00  --inst_passive_queue_type               priority_queues
% 2.10/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.10/1.00  --inst_passive_queues_freq              [25;2]
% 2.10/1.00  --inst_dismatching                      true
% 2.10/1.00  --inst_eager_unprocessed_to_passive     true
% 2.10/1.00  --inst_prop_sim_given                   true
% 2.10/1.00  --inst_prop_sim_new                     false
% 2.10/1.00  --inst_subs_new                         false
% 2.10/1.00  --inst_eq_res_simp                      false
% 2.10/1.00  --inst_subs_given                       false
% 2.10/1.00  --inst_orphan_elimination               true
% 2.10/1.00  --inst_learning_loop_flag               true
% 2.10/1.00  --inst_learning_start                   3000
% 2.10/1.00  --inst_learning_factor                  2
% 2.10/1.00  --inst_start_prop_sim_after_learn       3
% 2.10/1.00  --inst_sel_renew                        solver
% 2.10/1.00  --inst_lit_activity_flag                true
% 2.10/1.00  --inst_restr_to_given                   false
% 2.10/1.00  --inst_activity_threshold               500
% 2.10/1.00  --inst_out_proof                        true
% 2.10/1.00  
% 2.10/1.00  ------ Resolution Options
% 2.10/1.00  
% 2.10/1.00  --resolution_flag                       false
% 2.10/1.00  --res_lit_sel                           adaptive
% 2.10/1.00  --res_lit_sel_side                      none
% 2.10/1.00  --res_ordering                          kbo
% 2.10/1.00  --res_to_prop_solver                    active
% 2.10/1.00  --res_prop_simpl_new                    false
% 2.10/1.00  --res_prop_simpl_given                  true
% 2.10/1.00  --res_passive_queue_type                priority_queues
% 2.10/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.10/1.00  --res_passive_queues_freq               [15;5]
% 2.10/1.00  --res_forward_subs                      full
% 2.10/1.00  --res_backward_subs                     full
% 2.10/1.00  --res_forward_subs_resolution           true
% 2.10/1.00  --res_backward_subs_resolution          true
% 2.10/1.00  --res_orphan_elimination                true
% 2.10/1.00  --res_time_limit                        2.
% 2.10/1.00  --res_out_proof                         true
% 2.10/1.00  
% 2.10/1.00  ------ Superposition Options
% 2.10/1.00  
% 2.10/1.00  --superposition_flag                    true
% 2.10/1.00  --sup_passive_queue_type                priority_queues
% 2.10/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.10/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.10/1.00  --demod_completeness_check              fast
% 2.10/1.00  --demod_use_ground                      true
% 2.10/1.00  --sup_to_prop_solver                    passive
% 2.10/1.00  --sup_prop_simpl_new                    true
% 2.10/1.00  --sup_prop_simpl_given                  true
% 2.10/1.00  --sup_fun_splitting                     false
% 2.10/1.00  --sup_smt_interval                      50000
% 2.10/1.00  
% 2.10/1.00  ------ Superposition Simplification Setup
% 2.10/1.00  
% 2.10/1.00  --sup_indices_passive                   []
% 2.10/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.10/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_full_bw                           [BwDemod]
% 2.10/1.00  --sup_immed_triv                        [TrivRules]
% 2.10/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.10/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_immed_bw_main                     []
% 2.10/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.10/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.00  
% 2.10/1.00  ------ Combination Options
% 2.10/1.00  
% 2.10/1.00  --comb_res_mult                         3
% 2.10/1.00  --comb_sup_mult                         2
% 2.10/1.00  --comb_inst_mult                        10
% 2.10/1.00  
% 2.10/1.00  ------ Debug Options
% 2.10/1.00  
% 2.10/1.00  --dbg_backtrace                         false
% 2.10/1.00  --dbg_dump_prop_clauses                 false
% 2.10/1.00  --dbg_dump_prop_clauses_file            -
% 2.10/1.00  --dbg_out_stat                          false
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  ------ Proving...
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  % SZS status Theorem for theBenchmark.p
% 2.10/1.00  
% 2.10/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.10/1.00  
% 2.10/1.00  fof(f7,conjecture,(
% 2.10/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f8,negated_conjecture,(
% 2.10/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.10/1.00    inference(negated_conjecture,[],[f7])).
% 2.10/1.00  
% 2.10/1.00  fof(f20,plain,(
% 2.10/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.10/1.00    inference(ennf_transformation,[],[f8])).
% 2.10/1.00  
% 2.10/1.00  fof(f21,plain,(
% 2.10/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.10/1.00    inference(flattening,[],[f20])).
% 2.10/1.00  
% 2.10/1.00  fof(f23,plain,(
% 2.10/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.10/1.00    inference(nnf_transformation,[],[f21])).
% 2.10/1.00  
% 2.10/1.00  fof(f24,plain,(
% 2.10/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.10/1.00    inference(flattening,[],[f23])).
% 2.10/1.00  
% 2.10/1.00  fof(f32,plain,(
% 2.10/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) | r1_tmap_1(X3,X1,X4,X6)) & sK7 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 2.10/1.00    introduced(choice_axiom,[])).
% 2.10/1.00  
% 2.10/1.00  fof(f31,plain,(
% 2.10/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,sK6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,sK6)) & sK6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.10/1.00    introduced(choice_axiom,[])).
% 2.10/1.00  
% 2.10/1.00  fof(f30,plain,(
% 2.10/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(X2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))))) )),
% 2.10/1.00    introduced(choice_axiom,[])).
% 2.10/1.00  
% 2.10/1.00  fof(f29,plain,(
% 2.10/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X7) | ~r1_tmap_1(X3,X1,sK4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X7) | r1_tmap_1(X3,X1,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.10/1.00    introduced(choice_axiom,[])).
% 2.10/1.00  
% 2.10/1.00  fof(f28,plain,(
% 2.10/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X7) | ~r1_tmap_1(sK3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X7) | r1_tmap_1(sK3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.10/1.00    introduced(choice_axiom,[])).
% 2.10/1.00  
% 2.10/1.00  fof(f27,plain,(
% 2.10/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.10/1.00    introduced(choice_axiom,[])).
% 2.10/1.00  
% 2.10/1.00  fof(f26,plain,(
% 2.10/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.10/1.00    introduced(choice_axiom,[])).
% 2.10/1.00  
% 2.10/1.00  fof(f25,plain,(
% 2.10/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.10/1.00    introduced(choice_axiom,[])).
% 2.10/1.00  
% 2.10/1.00  fof(f33,plain,(
% 2.10/1.00    ((((((((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK3) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f24,f32,f31,f30,f29,f28,f27,f26,f25])).
% 2.10/1.00  
% 2.10/1.00  fof(f48,plain,(
% 2.10/1.00    m1_pre_topc(sK2,sK0)),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f4,axiom,(
% 2.10/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f14,plain,(
% 2.10/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/1.00    inference(ennf_transformation,[],[f4])).
% 2.10/1.00  
% 2.10/1.00  fof(f15,plain,(
% 2.10/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/1.00    inference(flattening,[],[f14])).
% 2.10/1.00  
% 2.10/1.00  fof(f37,plain,(
% 2.10/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f15])).
% 2.10/1.00  
% 2.10/1.00  fof(f52,plain,(
% 2.10/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f51,plain,(
% 2.10/1.00    v1_funct_1(sK4)),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f44,plain,(
% 2.10/1.00    ~v2_struct_0(sK1)),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f45,plain,(
% 2.10/1.00    v2_pre_topc(sK1)),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f46,plain,(
% 2.10/1.00    l1_pre_topc(sK1)),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f53,plain,(
% 2.10/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f54,plain,(
% 2.10/1.00    m1_pre_topc(sK2,sK3)),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f3,axiom,(
% 2.10/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f12,plain,(
% 2.10/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/1.00    inference(ennf_transformation,[],[f3])).
% 2.10/1.00  
% 2.10/1.00  fof(f13,plain,(
% 2.10/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/1.00    inference(flattening,[],[f12])).
% 2.10/1.00  
% 2.10/1.00  fof(f36,plain,(
% 2.10/1.00    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f13])).
% 2.10/1.00  
% 2.10/1.00  fof(f42,plain,(
% 2.10/1.00    v2_pre_topc(sK0)),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f43,plain,(
% 2.10/1.00    l1_pre_topc(sK0)),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f49,plain,(
% 2.10/1.00    ~v2_struct_0(sK3)),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f50,plain,(
% 2.10/1.00    m1_pre_topc(sK3,sK0)),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f2,axiom,(
% 2.10/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f11,plain,(
% 2.10/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.10/1.00    inference(ennf_transformation,[],[f2])).
% 2.10/1.00  
% 2.10/1.00  fof(f35,plain,(
% 2.10/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f11])).
% 2.10/1.00  
% 2.10/1.00  fof(f1,axiom,(
% 2.10/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f9,plain,(
% 2.10/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.10/1.00    inference(ennf_transformation,[],[f1])).
% 2.10/1.00  
% 2.10/1.00  fof(f10,plain,(
% 2.10/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.10/1.00    inference(flattening,[],[f9])).
% 2.10/1.00  
% 2.10/1.00  fof(f34,plain,(
% 2.10/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f10])).
% 2.10/1.00  
% 2.10/1.00  fof(f41,plain,(
% 2.10/1.00    ~v2_struct_0(sK0)),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f62,plain,(
% 2.10/1.00    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f61,plain,(
% 2.10/1.00    sK6 = sK7),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f6,axiom,(
% 2.10/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 2.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f18,plain,(
% 2.10/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/1.00    inference(ennf_transformation,[],[f6])).
% 2.10/1.00  
% 2.10/1.00  fof(f19,plain,(
% 2.10/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/1.00    inference(flattening,[],[f18])).
% 2.10/1.00  
% 2.10/1.00  fof(f40,plain,(
% 2.10/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f19])).
% 2.10/1.00  
% 2.10/1.00  fof(f66,plain,(
% 2.10/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/1.00    inference(equality_resolution,[],[f40])).
% 2.10/1.00  
% 2.10/1.00  fof(f58,plain,(
% 2.10/1.00    v3_pre_topc(sK5,sK3)),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f59,plain,(
% 2.10/1.00    r2_hidden(sK6,sK5)),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f5,axiom,(
% 2.10/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f16,plain,(
% 2.10/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/1.00    inference(ennf_transformation,[],[f5])).
% 2.10/1.00  
% 2.10/1.00  fof(f17,plain,(
% 2.10/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/1.00    inference(flattening,[],[f16])).
% 2.10/1.00  
% 2.10/1.00  fof(f22,plain,(
% 2.10/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/1.00    inference(nnf_transformation,[],[f17])).
% 2.10/1.00  
% 2.10/1.00  fof(f39,plain,(
% 2.10/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f22])).
% 2.10/1.00  
% 2.10/1.00  fof(f64,plain,(
% 2.10/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/1.00    inference(equality_resolution,[],[f39])).
% 2.10/1.00  
% 2.10/1.00  fof(f60,plain,(
% 2.10/1.00    r1_tarski(sK5,u1_struct_0(sK2))),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f55,plain,(
% 2.10/1.00    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f56,plain,(
% 2.10/1.00    m1_subset_1(sK6,u1_struct_0(sK3))),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f47,plain,(
% 2.10/1.00    ~v2_struct_0(sK2)),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f57,plain,(
% 2.10/1.00    m1_subset_1(sK7,u1_struct_0(sK2))),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f63,plain,(
% 2.10/1.00    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  cnf(c_22,negated_conjecture,
% 2.10/1.00      ( m1_pre_topc(sK2,sK0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1236,negated_conjecture,
% 2.10/1.00      ( m1_pre_topc(sK2,sK0) ),
% 2.10/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1879,plain,
% 2.10/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1236]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3,plain,
% 2.10/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.10/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.10/1.00      | ~ m1_pre_topc(X3,X4)
% 2.10/1.00      | ~ m1_pre_topc(X3,X1)
% 2.10/1.00      | ~ m1_pre_topc(X1,X4)
% 2.10/1.00      | v2_struct_0(X4)
% 2.10/1.00      | v2_struct_0(X2)
% 2.10/1.00      | ~ v1_funct_1(X0)
% 2.10/1.00      | ~ l1_pre_topc(X4)
% 2.10/1.00      | ~ l1_pre_topc(X2)
% 2.10/1.00      | ~ v2_pre_topc(X4)
% 2.10/1.00      | ~ v2_pre_topc(X2)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_18,negated_conjecture,
% 2.10/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 2.10/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_727,plain,
% 2.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.10/1.00      | ~ m1_pre_topc(X3,X1)
% 2.10/1.00      | ~ m1_pre_topc(X3,X4)
% 2.10/1.00      | ~ m1_pre_topc(X1,X4)
% 2.10/1.00      | v2_struct_0(X2)
% 2.10/1.00      | v2_struct_0(X4)
% 2.10/1.00      | ~ v1_funct_1(X0)
% 2.10/1.00      | ~ l1_pre_topc(X2)
% 2.10/1.00      | ~ l1_pre_topc(X4)
% 2.10/1.00      | ~ v2_pre_topc(X2)
% 2.10/1.00      | ~ v2_pre_topc(X4)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0)
% 2.10/1.00      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.10/1.00      | sK4 != X0 ),
% 2.10/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_18]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_728,plain,
% 2.10/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.10/1.00      | ~ m1_pre_topc(X2,X0)
% 2.10/1.00      | ~ m1_pre_topc(X2,X3)
% 2.10/1.00      | ~ m1_pre_topc(X0,X3)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X3)
% 2.10/1.00      | ~ v1_funct_1(sK4)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(X3)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X3)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 2.10/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.10/1.00      inference(unflattening,[status(thm)],[c_727]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_19,negated_conjecture,
% 2.10/1.00      ( v1_funct_1(sK4) ),
% 2.10/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_732,plain,
% 2.10/1.00      ( v2_struct_0(X3)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | ~ m1_pre_topc(X0,X3)
% 2.10/1.00      | ~ m1_pre_topc(X2,X3)
% 2.10/1.00      | ~ m1_pre_topc(X2,X0)
% 2.10/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(X3)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X3)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 2.10/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.10/1.00      inference(global_propositional_subsumption,
% 2.10/1.00                [status(thm)],
% 2.10/1.00                [c_728,c_19]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_733,plain,
% 2.10/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.10/1.00      | ~ m1_pre_topc(X2,X3)
% 2.10/1.00      | ~ m1_pre_topc(X2,X0)
% 2.10/1.00      | ~ m1_pre_topc(X0,X3)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X3)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(X3)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X3)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 2.10/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.10/1.00      inference(renaming,[status(thm)],[c_732]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1228,plain,
% 2.10/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 2.10/1.00      | ~ m1_pre_topc(X2_53,X3_53)
% 2.10/1.00      | ~ m1_pre_topc(X0_53,X3_53)
% 2.10/1.00      | ~ m1_pre_topc(X2_53,X0_53)
% 2.10/1.00      | v2_struct_0(X1_53)
% 2.10/1.00      | v2_struct_0(X3_53)
% 2.10/1.00      | ~ l1_pre_topc(X1_53)
% 2.10/1.00      | ~ l1_pre_topc(X3_53)
% 2.10/1.00      | ~ v2_pre_topc(X1_53)
% 2.10/1.00      | ~ v2_pre_topc(X3_53)
% 2.10/1.00      | u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK4,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4) ),
% 2.10/1.00      inference(subtyping,[status(esa)],[c_733]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1887,plain,
% 2.10/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK4,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4)
% 2.10/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.10/1.00      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 2.10/1.00      | m1_pre_topc(X2_53,X3_53) != iProver_top
% 2.10/1.00      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 2.10/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.10/1.00      | v2_struct_0(X3_53) = iProver_top
% 2.10/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.10/1.00      | l1_pre_topc(X3_53) != iProver_top
% 2.10/1.00      | v2_pre_topc(X1_53) != iProver_top
% 2.10/1.00      | v2_pre_topc(X3_53) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1228]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2954,plain,
% 2.10/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4)
% 2.10/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 2.10/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.10/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.10/1.00      | m1_pre_topc(X1_53,X2_53) != iProver_top
% 2.10/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.10/1.00      | v2_struct_0(sK1) = iProver_top
% 2.10/1.00      | l1_pre_topc(X2_53) != iProver_top
% 2.10/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.10/1.00      | v2_pre_topc(X2_53) != iProver_top
% 2.10/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.10/1.00      inference(equality_resolution,[status(thm)],[c_1887]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_26,negated_conjecture,
% 2.10/1.00      ( ~ v2_struct_0(sK1) ),
% 2.10/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_33,plain,
% 2.10/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_25,negated_conjecture,
% 2.10/1.00      ( v2_pre_topc(sK1) ),
% 2.10/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_34,plain,
% 2.10/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_24,negated_conjecture,
% 2.10/1.00      ( l1_pre_topc(sK1) ),
% 2.10/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_35,plain,
% 2.10/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2172,plain,
% 2.10/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1))))
% 2.10/1.00      | ~ m1_pre_topc(X0_53,X1_53)
% 2.10/1.00      | ~ m1_pre_topc(X2_53,X0_53)
% 2.10/1.00      | ~ m1_pre_topc(X2_53,X1_53)
% 2.10/1.00      | v2_struct_0(X1_53)
% 2.10/1.00      | v2_struct_0(sK1)
% 2.10/1.00      | ~ l1_pre_topc(X1_53)
% 2.10/1.00      | ~ l1_pre_topc(sK1)
% 2.10/1.00      | ~ v2_pre_topc(X1_53)
% 2.10/1.00      | ~ v2_pre_topc(sK1)
% 2.10/1.00      | u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X2_53)) = k3_tmap_1(X1_53,sK1,X0_53,X2_53,sK4) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_1228]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2173,plain,
% 2.10/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4)
% 2.10/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 2.10/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.10/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.10/1.00      | m1_pre_topc(X1_53,X2_53) != iProver_top
% 2.10/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.10/1.00      | v2_struct_0(sK1) = iProver_top
% 2.10/1.00      | l1_pre_topc(X2_53) != iProver_top
% 2.10/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.10/1.00      | v2_pre_topc(X2_53) != iProver_top
% 2.10/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_2172]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1255,plain,( X0_55 = X0_55 ),theory(equality) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2320,plain,
% 2.10/1.00      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_1255]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3111,plain,
% 2.10/1.00      ( v2_pre_topc(X2_53) != iProver_top
% 2.10/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.10/1.00      | m1_pre_topc(X1_53,X2_53) != iProver_top
% 2.10/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.10/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.10/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4)
% 2.10/1.00      | u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.10/1.00      | l1_pre_topc(X2_53) != iProver_top ),
% 2.10/1.00      inference(global_propositional_subsumption,
% 2.10/1.00                [status(thm)],
% 2.10/1.00                [c_2954,c_33,c_34,c_35,c_2173,c_2320]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3112,plain,
% 2.10/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4)
% 2.10/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 2.10/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.10/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.10/1.00      | m1_pre_topc(X1_53,X2_53) != iProver_top
% 2.10/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.10/1.00      | l1_pre_topc(X2_53) != iProver_top
% 2.10/1.00      | v2_pre_topc(X2_53) != iProver_top ),
% 2.10/1.00      inference(renaming,[status(thm)],[c_3111]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3126,plain,
% 2.10/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4)
% 2.10/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.10/1.00      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.10/1.00      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.10/1.00      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.10/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.10/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.10/1.00      | v2_pre_topc(X1_53) != iProver_top ),
% 2.10/1.00      inference(equality_resolution,[status(thm)],[c_3112]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_17,negated_conjecture,
% 2.10/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.10/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_42,plain,
% 2.10/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3322,plain,
% 2.10/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4)
% 2.10/1.00      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.10/1.00      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.10/1.00      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.10/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.10/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.10/1.00      | v2_pre_topc(X1_53) != iProver_top ),
% 2.10/1.00      inference(global_propositional_subsumption,
% 2.10/1.00                [status(thm)],
% 2.10/1.00                [c_3126,c_42]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3337,plain,
% 2.10/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
% 2.10/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.10/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.10/1.00      | v2_struct_0(sK0) = iProver_top
% 2.10/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.10/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 2.10/1.00      inference(superposition,[status(thm)],[c_1879,c_3322]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_16,negated_conjecture,
% 2.10/1.00      ( m1_pre_topc(sK2,sK3) ),
% 2.10/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1240,negated_conjecture,
% 2.10/1.00      ( m1_pre_topc(sK2,sK3) ),
% 2.10/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1875,plain,
% 2.10/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1240]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2,plain,
% 2.10/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.10/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.10/1.00      | ~ m1_pre_topc(X3,X1)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X2)
% 2.10/1.00      | ~ v1_funct_1(X0)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(X2)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X2)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.10/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_778,plain,
% 2.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.10/1.00      | ~ m1_pre_topc(X3,X1)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X2)
% 2.10/1.00      | ~ v1_funct_1(X0)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(X2)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X2)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 2.10/1.00      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.10/1.00      | sK4 != X0 ),
% 2.10/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_18]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_779,plain,
% 2.10/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.10/1.00      | ~ m1_pre_topc(X2,X0)
% 2.10/1.00      | v2_struct_0(X0)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | ~ v1_funct_1(sK4)
% 2.10/1.00      | ~ l1_pre_topc(X0)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X0)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
% 2.10/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.10/1.00      inference(unflattening,[status(thm)],[c_778]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_783,plain,
% 2.10/1.00      ( v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X0)
% 2.10/1.00      | ~ m1_pre_topc(X2,X0)
% 2.10/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.10/1.00      | ~ l1_pre_topc(X0)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X0)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
% 2.10/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.10/1.00      inference(global_propositional_subsumption,
% 2.10/1.00                [status(thm)],
% 2.10/1.00                [c_779,c_19]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_784,plain,
% 2.10/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.10/1.00      | ~ m1_pre_topc(X2,X0)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X0)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(X0)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X0)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
% 2.10/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.10/1.00      inference(renaming,[status(thm)],[c_783]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1227,plain,
% 2.10/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 2.10/1.00      | ~ m1_pre_topc(X2_53,X0_53)
% 2.10/1.00      | v2_struct_0(X1_53)
% 2.10/1.00      | v2_struct_0(X0_53)
% 2.10/1.00      | ~ l1_pre_topc(X1_53)
% 2.10/1.00      | ~ l1_pre_topc(X0_53)
% 2.10/1.00      | ~ v2_pre_topc(X1_53)
% 2.10/1.00      | ~ v2_pre_topc(X0_53)
% 2.10/1.00      | u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK4,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,sK4,X2_53) ),
% 2.10/1.00      inference(subtyping,[status(esa)],[c_784]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1888,plain,
% 2.10/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK4,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,sK4,X2_53)
% 2.10/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.10/1.00      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 2.10/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.10/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.10/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.10/1.00      | l1_pre_topc(X0_53) != iProver_top
% 2.10/1.00      | v2_pre_topc(X1_53) != iProver_top
% 2.10/1.00      | v2_pre_topc(X0_53) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1227]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2936,plain,
% 2.10/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k2_tmap_1(X0_53,sK1,sK4,X1_53)
% 2.10/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 2.10/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.10/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.10/1.00      | v2_struct_0(sK1) = iProver_top
% 2.10/1.00      | l1_pre_topc(X0_53) != iProver_top
% 2.10/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.10/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.10/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.10/1.00      inference(equality_resolution,[status(thm)],[c_1888]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2162,plain,
% 2.10/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1))))
% 2.10/1.00      | ~ m1_pre_topc(X1_53,X0_53)
% 2.10/1.00      | v2_struct_0(X0_53)
% 2.10/1.00      | v2_struct_0(sK1)
% 2.10/1.00      | ~ l1_pre_topc(X0_53)
% 2.10/1.00      | ~ l1_pre_topc(sK1)
% 2.10/1.00      | ~ v2_pre_topc(X0_53)
% 2.10/1.00      | ~ v2_pre_topc(sK1)
% 2.10/1.00      | u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k2_tmap_1(X0_53,sK1,sK4,X1_53) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_1227]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2163,plain,
% 2.10/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k2_tmap_1(X0_53,sK1,sK4,X1_53)
% 2.10/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 2.10/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.10/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.10/1.00      | v2_struct_0(sK1) = iProver_top
% 2.10/1.00      | l1_pre_topc(X0_53) != iProver_top
% 2.10/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.10/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.10/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_2162]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3036,plain,
% 2.10/1.00      ( v2_pre_topc(X0_53) != iProver_top
% 2.10/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.10/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.10/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k2_tmap_1(X0_53,sK1,sK4,X1_53)
% 2.10/1.00      | u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.10/1.00      | l1_pre_topc(X0_53) != iProver_top ),
% 2.10/1.00      inference(global_propositional_subsumption,
% 2.10/1.00                [status(thm)],
% 2.10/1.00                [c_2936,c_33,c_34,c_35,c_2163,c_2320]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3037,plain,
% 2.10/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.10/1.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k2_tmap_1(X0_53,sK1,sK4,X1_53)
% 2.10/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 2.10/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.10/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.10/1.00      | l1_pre_topc(X0_53) != iProver_top
% 2.10/1.00      | v2_pre_topc(X0_53) != iProver_top ),
% 2.10/1.00      inference(renaming,[status(thm)],[c_3036]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3049,plain,
% 2.10/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK3,sK1,sK4,X0_53)
% 2.10/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.10/1.00      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.10/1.00      | v2_struct_0(sK3) = iProver_top
% 2.10/1.00      | l1_pre_topc(sK3) != iProver_top
% 2.10/1.00      | v2_pre_topc(sK3) != iProver_top ),
% 2.10/1.00      inference(equality_resolution,[status(thm)],[c_3037]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_28,negated_conjecture,
% 2.10/1.00      ( v2_pre_topc(sK0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_31,plain,
% 2.10/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_27,negated_conjecture,
% 2.10/1.00      ( l1_pre_topc(sK0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_32,plain,
% 2.10/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_21,negated_conjecture,
% 2.10/1.00      ( ~ v2_struct_0(sK3) ),
% 2.10/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_38,plain,
% 2.10/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_20,negated_conjecture,
% 2.10/1.00      ( m1_pre_topc(sK3,sK0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_39,plain,
% 2.10/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1,plain,
% 2.10/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1247,plain,
% 2.10/1.00      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.10/1.00      | ~ l1_pre_topc(X1_53)
% 2.10/1.00      | l1_pre_topc(X0_53) ),
% 2.10/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2197,plain,
% 2.10/1.00      ( ~ m1_pre_topc(X0_53,sK0)
% 2.10/1.00      | l1_pre_topc(X0_53)
% 2.10/1.00      | ~ l1_pre_topc(sK0) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_1247]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2198,plain,
% 2.10/1.00      ( m1_pre_topc(X0_53,sK0) != iProver_top
% 2.10/1.00      | l1_pre_topc(X0_53) = iProver_top
% 2.10/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_2197]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2200,plain,
% 2.10/1.00      ( m1_pre_topc(sK3,sK0) != iProver_top
% 2.10/1.00      | l1_pre_topc(sK3) = iProver_top
% 2.10/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_2198]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_0,plain,
% 2.10/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | v2_pre_topc(X0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1248,plain,
% 2.10/1.00      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.10/1.00      | ~ l1_pre_topc(X1_53)
% 2.10/1.00      | ~ v2_pre_topc(X1_53)
% 2.10/1.00      | v2_pre_topc(X0_53) ),
% 2.10/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2207,plain,
% 2.10/1.00      ( ~ m1_pre_topc(X0_53,sK0)
% 2.10/1.00      | ~ l1_pre_topc(sK0)
% 2.10/1.00      | v2_pre_topc(X0_53)
% 2.10/1.00      | ~ v2_pre_topc(sK0) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_1248]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2208,plain,
% 2.10/1.00      ( m1_pre_topc(X0_53,sK0) != iProver_top
% 2.10/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.10/1.00      | v2_pre_topc(X0_53) = iProver_top
% 2.10/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_2207]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2210,plain,
% 2.10/1.00      ( m1_pre_topc(sK3,sK0) != iProver_top
% 2.10/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.10/1.00      | v2_pre_topc(sK3) = iProver_top
% 2.10/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_2208]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3263,plain,
% 2.10/1.00      ( m1_pre_topc(X0_53,sK3) != iProver_top
% 2.10/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK3,sK1,sK4,X0_53) ),
% 2.10/1.00      inference(global_propositional_subsumption,
% 2.10/1.00                [status(thm)],
% 2.10/1.00                [c_3049,c_31,c_32,c_38,c_39,c_42,c_2200,c_2210]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3264,plain,
% 2.10/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK3,sK1,sK4,X0_53)
% 2.10/1.00      | m1_pre_topc(X0_53,sK3) != iProver_top ),
% 2.10/1.00      inference(renaming,[status(thm)],[c_3263]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3271,plain,
% 2.10/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
% 2.10/1.00      inference(superposition,[status(thm)],[c_1875,c_3264]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3344,plain,
% 2.10/1.00      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)
% 2.10/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.10/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.10/1.00      | v2_struct_0(sK0) = iProver_top
% 2.10/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.10/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 2.10/1.00      inference(light_normalisation,[status(thm)],[c_3337,c_3271]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_29,negated_conjecture,
% 2.10/1.00      ( ~ v2_struct_0(sK0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_30,plain,
% 2.10/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_43,plain,
% 2.10/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3434,plain,
% 2.10/1.00      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
% 2.10/1.00      inference(global_propositional_subsumption,
% 2.10/1.00                [status(thm)],
% 2.10/1.00                [c_3344,c_30,c_31,c_32,c_39,c_43]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_8,negated_conjecture,
% 2.10/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK6)
% 2.10/1.00      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 2.10/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1245,negated_conjecture,
% 2.10/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK6)
% 2.10/1.00      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 2.10/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1871,plain,
% 2.10/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK6) = iProver_top
% 2.10/1.00      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1245]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_9,negated_conjecture,
% 2.10/1.00      ( sK6 = sK7 ),
% 2.10/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1244,negated_conjecture,
% 2.10/1.00      ( sK6 = sK7 ),
% 2.10/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1945,plain,
% 2.10/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 2.10/1.00      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
% 2.10/1.00      inference(light_normalisation,[status(thm)],[c_1871,c_1244]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3437,plain,
% 2.10/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 2.10/1.00      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) = iProver_top ),
% 2.10/1.00      inference(demodulation,[status(thm)],[c_3434,c_1945]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_6,plain,
% 2.10/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.10/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.10/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.10/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.10/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.10/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.10/1.00      | ~ m1_pre_topc(X4,X5)
% 2.10/1.00      | ~ m1_pre_topc(X4,X0)
% 2.10/1.00      | ~ m1_pre_topc(X0,X5)
% 2.10/1.00      | v2_struct_0(X5)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X0)
% 2.10/1.00      | v2_struct_0(X4)
% 2.10/1.00      | ~ v1_funct_1(X2)
% 2.10/1.00      | ~ l1_pre_topc(X5)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X5)
% 2.10/1.00      | ~ v2_pre_topc(X1) ),
% 2.10/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_823,plain,
% 2.10/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.10/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.10/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.10/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.10/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.10/1.00      | ~ m1_pre_topc(X4,X0)
% 2.10/1.00      | ~ m1_pre_topc(X4,X5)
% 2.10/1.00      | ~ m1_pre_topc(X0,X5)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X0)
% 2.10/1.00      | v2_struct_0(X4)
% 2.10/1.00      | v2_struct_0(X5)
% 2.10/1.00      | ~ v1_funct_1(X2)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(X5)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X5)
% 2.10/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.10/1.00      | sK4 != X2 ),
% 2.10/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_824,plain,
% 2.10/1.00      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.10/1.00      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.10/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.10/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.10/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.10/1.00      | ~ m1_pre_topc(X0,X3)
% 2.10/1.00      | ~ m1_pre_topc(X0,X2)
% 2.10/1.00      | ~ m1_pre_topc(X3,X2)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X3)
% 2.10/1.00      | v2_struct_0(X0)
% 2.10/1.00      | v2_struct_0(X2)
% 2.10/1.00      | ~ v1_funct_1(sK4)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(X2)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X2)
% 2.10/1.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.10/1.00      inference(unflattening,[status(thm)],[c_823]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_828,plain,
% 2.10/1.00      ( v2_struct_0(X2)
% 2.10/1.00      | v2_struct_0(X0)
% 2.10/1.00      | v2_struct_0(X3)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | ~ m1_pre_topc(X3,X2)
% 2.10/1.00      | ~ m1_pre_topc(X0,X2)
% 2.10/1.00      | ~ m1_pre_topc(X0,X3)
% 2.10/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.10/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.10/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.10/1.00      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.10/1.00      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(X2)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X2)
% 2.10/1.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.10/1.00      inference(global_propositional_subsumption,
% 2.10/1.00                [status(thm)],
% 2.10/1.00                [c_824,c_19]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_829,plain,
% 2.10/1.00      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.10/1.00      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.10/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.10/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.10/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.10/1.00      | ~ m1_pre_topc(X3,X2)
% 2.10/1.00      | ~ m1_pre_topc(X0,X3)
% 2.10/1.00      | ~ m1_pre_topc(X0,X2)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X0)
% 2.10/1.00      | v2_struct_0(X2)
% 2.10/1.00      | v2_struct_0(X3)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(X2)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X2)
% 2.10/1.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.10/1.00      inference(renaming,[status(thm)],[c_828]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1226,plain,
% 2.10/1.00      ( r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),X0_54)
% 2.10/1.00      | ~ r1_tmap_1(X3_53,X1_53,sK4,X0_54)
% 2.10/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 2.10/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(X3_53))
% 2.10/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
% 2.10/1.00      | ~ m1_pre_topc(X3_53,X2_53)
% 2.10/1.00      | ~ m1_pre_topc(X0_53,X3_53)
% 2.10/1.00      | ~ m1_pre_topc(X0_53,X2_53)
% 2.10/1.00      | v2_struct_0(X1_53)
% 2.10/1.00      | v2_struct_0(X0_53)
% 2.10/1.00      | v2_struct_0(X2_53)
% 2.10/1.00      | v2_struct_0(X3_53)
% 2.10/1.00      | ~ l1_pre_topc(X1_53)
% 2.10/1.00      | ~ l1_pre_topc(X2_53)
% 2.10/1.00      | ~ v2_pre_topc(X1_53)
% 2.10/1.00      | ~ v2_pre_topc(X2_53)
% 2.10/1.00      | u1_struct_0(X3_53) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(X1_53) != u1_struct_0(sK1) ),
% 2.10/1.00      inference(subtyping,[status(esa)],[c_829]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2182,plain,
% 2.10/1.00      ( r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,X2_53,X0_53,sK4),X0_54)
% 2.10/1.00      | ~ r1_tmap_1(X2_53,sK1,sK4,X0_54)
% 2.10/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 2.10/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(X2_53))
% 2.10/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(sK1))))
% 2.10/1.00      | ~ m1_pre_topc(X0_53,X2_53)
% 2.10/1.00      | ~ m1_pre_topc(X0_53,X1_53)
% 2.10/1.00      | ~ m1_pre_topc(X2_53,X1_53)
% 2.10/1.00      | v2_struct_0(X1_53)
% 2.10/1.00      | v2_struct_0(X0_53)
% 2.10/1.00      | v2_struct_0(X2_53)
% 2.10/1.00      | v2_struct_0(sK1)
% 2.10/1.00      | ~ l1_pre_topc(X1_53)
% 2.10/1.00      | ~ l1_pre_topc(sK1)
% 2.10/1.00      | ~ v2_pre_topc(X1_53)
% 2.10/1.00      | ~ v2_pre_topc(sK1)
% 2.10/1.00      | u1_struct_0(X2_53) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_1226]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2410,plain,
% 2.10/1.00      ( ~ r1_tmap_1(sK3,sK1,sK4,X0_54)
% 2.10/1.00      | r1_tmap_1(sK2,sK1,k3_tmap_1(X0_53,sK1,sK3,sK2,sK4),X0_54)
% 2.10/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.10/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 2.10/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.10/1.00      | ~ m1_pre_topc(sK3,X0_53)
% 2.10/1.00      | ~ m1_pre_topc(sK2,X0_53)
% 2.10/1.00      | ~ m1_pre_topc(sK2,sK3)
% 2.10/1.00      | v2_struct_0(X0_53)
% 2.10/1.00      | v2_struct_0(sK3)
% 2.10/1.00      | v2_struct_0(sK1)
% 2.10/1.00      | v2_struct_0(sK2)
% 2.10/1.00      | ~ l1_pre_topc(X0_53)
% 2.10/1.00      | ~ l1_pre_topc(sK1)
% 2.10/1.00      | ~ v2_pre_topc(X0_53)
% 2.10/1.00      | ~ v2_pre_topc(sK1)
% 2.10/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_2182]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2794,plain,
% 2.10/1.00      ( ~ r1_tmap_1(sK3,sK1,sK4,X0_54)
% 2.10/1.00      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0_54)
% 2.10/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.10/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 2.10/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.10/1.00      | ~ m1_pre_topc(sK3,sK0)
% 2.10/1.00      | ~ m1_pre_topc(sK2,sK3)
% 2.10/1.00      | ~ m1_pre_topc(sK2,sK0)
% 2.10/1.00      | v2_struct_0(sK3)
% 2.10/1.00      | v2_struct_0(sK0)
% 2.10/1.00      | v2_struct_0(sK1)
% 2.10/1.00      | v2_struct_0(sK2)
% 2.10/1.00      | ~ l1_pre_topc(sK0)
% 2.10/1.00      | ~ l1_pre_topc(sK1)
% 2.10/1.00      | ~ v2_pre_topc(sK0)
% 2.10/1.00      | ~ v2_pre_topc(sK1)
% 2.10/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_2410]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3304,plain,
% 2.10/1.00      ( ~ r1_tmap_1(sK3,sK1,sK4,sK7)
% 2.10/1.00      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
% 2.10/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.10/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK2))
% 2.10/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.10/1.00      | ~ m1_pre_topc(sK3,sK0)
% 2.10/1.00      | ~ m1_pre_topc(sK2,sK3)
% 2.10/1.00      | ~ m1_pre_topc(sK2,sK0)
% 2.10/1.00      | v2_struct_0(sK3)
% 2.10/1.00      | v2_struct_0(sK0)
% 2.10/1.00      | v2_struct_0(sK1)
% 2.10/1.00      | v2_struct_0(sK2)
% 2.10/1.00      | ~ l1_pre_topc(sK0)
% 2.10/1.00      | ~ l1_pre_topc(sK1)
% 2.10/1.00      | ~ v2_pre_topc(sK0)
% 2.10/1.00      | ~ v2_pre_topc(sK1)
% 2.10/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_2794]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3307,plain,
% 2.10/1.00      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.10/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.10/1.00      | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 2.10/1.00      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top
% 2.10/1.00      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.10/1.00      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
% 2.10/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.10/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.10/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.10/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.10/1.00      | v2_struct_0(sK3) = iProver_top
% 2.10/1.00      | v2_struct_0(sK0) = iProver_top
% 2.10/1.00      | v2_struct_0(sK1) = iProver_top
% 2.10/1.00      | v2_struct_0(sK2) = iProver_top
% 2.10/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.10/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.10/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.10/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_3304]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_12,negated_conjecture,
% 2.10/1.00      ( v3_pre_topc(sK5,sK3) ),
% 2.10/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_11,negated_conjecture,
% 2.10/1.00      ( r2_hidden(sK6,sK5) ),
% 2.10/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_4,plain,
% 2.10/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.10/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.10/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.10/1.00      | ~ v3_pre_topc(X5,X0)
% 2.10/1.00      | ~ r2_hidden(X3,X5)
% 2.10/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.10/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.10/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.10/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.10/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.10/1.00      | ~ m1_pre_topc(X4,X0)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X0)
% 2.10/1.00      | v2_struct_0(X4)
% 2.10/1.00      | ~ v1_funct_1(X2)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(X0)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_10,negated_conjecture,
% 2.10/1.00      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 2.10/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_430,plain,
% 2.10/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.10/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.10/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.10/1.00      | ~ v3_pre_topc(X5,X0)
% 2.10/1.00      | ~ r2_hidden(X3,X5)
% 2.10/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.10/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.10/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.10/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.10/1.00      | ~ m1_pre_topc(X4,X0)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X0)
% 2.10/1.00      | v2_struct_0(X4)
% 2.10/1.00      | ~ v1_funct_1(X2)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(X0)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X0)
% 2.10/1.00      | u1_struct_0(X4) != u1_struct_0(sK2)
% 2.10/1.00      | sK5 != X5 ),
% 2.10/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_10]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_431,plain,
% 2.10/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.10/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.10/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.10/1.00      | ~ v3_pre_topc(sK5,X0)
% 2.10/1.00      | ~ r2_hidden(X3,sK5)
% 2.10/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.10/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.10/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.10/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.10/1.00      | ~ m1_pre_topc(X4,X0)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X0)
% 2.10/1.00      | v2_struct_0(X4)
% 2.10/1.00      | ~ v1_funct_1(X2)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(X0)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X0)
% 2.10/1.00      | u1_struct_0(X4) != u1_struct_0(sK2) ),
% 2.10/1.00      inference(unflattening,[status(thm)],[c_430]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_495,plain,
% 2.10/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.10/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.10/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.10/1.00      | ~ v3_pre_topc(sK5,X0)
% 2.10/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.10/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.10/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.10/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.10/1.00      | ~ m1_pre_topc(X4,X0)
% 2.10/1.00      | v2_struct_0(X0)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X4)
% 2.10/1.00      | ~ v1_funct_1(X2)
% 2.10/1.00      | ~ l1_pre_topc(X0)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X0)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | u1_struct_0(X4) != u1_struct_0(sK2)
% 2.10/1.00      | sK5 != sK5
% 2.10/1.00      | sK6 != X3 ),
% 2.10/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_431]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_496,plain,
% 2.10/1.00      ( r1_tmap_1(X0,X1,X2,sK6)
% 2.10/1.00      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
% 2.10/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.10/1.00      | ~ v3_pre_topc(sK5,X0)
% 2.10/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.10/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.10/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.10/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.10/1.00      | ~ m1_pre_topc(X3,X0)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X0)
% 2.10/1.00      | v2_struct_0(X3)
% 2.10/1.00      | ~ v1_funct_1(X2)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(X0)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X0)
% 2.10/1.00      | u1_struct_0(X3) != u1_struct_0(sK2) ),
% 2.10/1.00      inference(unflattening,[status(thm)],[c_495]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_671,plain,
% 2.10/1.00      ( r1_tmap_1(X0,X1,X2,sK6)
% 2.10/1.00      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
% 2.10/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.10/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.10/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.10/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.10/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.10/1.00      | ~ m1_pre_topc(X3,X0)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X0)
% 2.10/1.00      | v2_struct_0(X3)
% 2.10/1.00      | ~ v1_funct_1(X2)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(X0)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(X0)
% 2.10/1.00      | u1_struct_0(X3) != u1_struct_0(sK2)
% 2.10/1.00      | sK5 != sK5
% 2.10/1.00      | sK3 != X0 ),
% 2.10/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_496]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_672,plain,
% 2.10/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
% 2.10/1.00      | r1_tmap_1(sK3,X1,X2,sK6)
% 2.10/1.00      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
% 2.10/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.10/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.10/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.10/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.10/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X0)
% 2.10/1.00      | v2_struct_0(sK3)
% 2.10/1.00      | ~ v1_funct_1(X2)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(sK3)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(sK3)
% 2.10/1.00      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.10/1.00      inference(unflattening,[status(thm)],[c_671]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_15,negated_conjecture,
% 2.10/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.10/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_14,negated_conjecture,
% 2.10/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.10/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_676,plain,
% 2.10/1.00      ( v2_struct_0(X0)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.10/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.10/1.00      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
% 2.10/1.00      | r1_tmap_1(sK3,X1,X2,sK6)
% 2.10/1.00      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
% 2.10/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.10/1.00      | ~ v1_funct_1(X2)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(sK3)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(sK3)
% 2.10/1.00      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.10/1.00      inference(global_propositional_subsumption,
% 2.10/1.00                [status(thm)],
% 2.10/1.00                [c_672,c_21,c_15,c_14]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_677,plain,
% 2.10/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
% 2.10/1.00      | r1_tmap_1(sK3,X1,X2,sK6)
% 2.10/1.00      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
% 2.10/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.10/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.10/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.10/1.00      | v2_struct_0(X1)
% 2.10/1.00      | v2_struct_0(X0)
% 2.10/1.00      | ~ v1_funct_1(X2)
% 2.10/1.00      | ~ l1_pre_topc(X1)
% 2.10/1.00      | ~ l1_pre_topc(sK3)
% 2.10/1.00      | ~ v2_pre_topc(X1)
% 2.10/1.00      | ~ v2_pre_topc(sK3)
% 2.10/1.01      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.10/1.01      inference(renaming,[status(thm)],[c_676]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_889,plain,
% 2.10/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,X2,X0),sK6)
% 2.10/1.01      | r1_tmap_1(sK3,X1,X2,sK6)
% 2.10/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.10/1.01      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.10/1.01      | ~ m1_pre_topc(X0,sK3)
% 2.10/1.01      | v2_struct_0(X1)
% 2.10/1.01      | v2_struct_0(X0)
% 2.10/1.01      | ~ v1_funct_1(X2)
% 2.10/1.01      | ~ l1_pre_topc(X1)
% 2.10/1.01      | ~ l1_pre_topc(sK3)
% 2.10/1.01      | ~ v2_pre_topc(X1)
% 2.10/1.01      | ~ v2_pre_topc(sK3)
% 2.10/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.10/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.10/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.10/1.01      | sK4 != X2 ),
% 2.10/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_677]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_890,plain,
% 2.10/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
% 2.10/1.01      | r1_tmap_1(sK3,X1,sK4,sK6)
% 2.10/1.01      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.10/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.10/1.01      | ~ m1_pre_topc(X0,sK3)
% 2.10/1.01      | v2_struct_0(X1)
% 2.10/1.01      | v2_struct_0(X0)
% 2.10/1.01      | ~ v1_funct_1(sK4)
% 2.10/1.01      | ~ l1_pre_topc(X1)
% 2.10/1.01      | ~ l1_pre_topc(sK3)
% 2.10/1.01      | ~ v2_pre_topc(X1)
% 2.10/1.01      | ~ v2_pre_topc(sK3)
% 2.10/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.10/1.01      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.10/1.01      inference(unflattening,[status(thm)],[c_889]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_894,plain,
% 2.10/1.01      ( v2_struct_0(X0)
% 2.10/1.01      | v2_struct_0(X1)
% 2.10/1.01      | ~ m1_pre_topc(X0,sK3)
% 2.10/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.10/1.01      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.10/1.01      | r1_tmap_1(sK3,X1,sK4,sK6)
% 2.10/1.01      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
% 2.10/1.01      | ~ l1_pre_topc(X1)
% 2.10/1.01      | ~ l1_pre_topc(sK3)
% 2.10/1.01      | ~ v2_pre_topc(X1)
% 2.10/1.01      | ~ v2_pre_topc(sK3)
% 2.10/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.10/1.01      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.10/1.01      inference(global_propositional_subsumption,
% 2.10/1.01                [status(thm)],
% 2.10/1.01                [c_890,c_19]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_895,plain,
% 2.10/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),sK6)
% 2.10/1.01      | r1_tmap_1(sK3,X1,sK4,sK6)
% 2.10/1.01      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.10/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.10/1.01      | ~ m1_pre_topc(X0,sK3)
% 2.10/1.01      | v2_struct_0(X1)
% 2.10/1.01      | v2_struct_0(X0)
% 2.10/1.01      | ~ l1_pre_topc(X1)
% 2.10/1.01      | ~ l1_pre_topc(sK3)
% 2.10/1.01      | ~ v2_pre_topc(X1)
% 2.10/1.01      | ~ v2_pre_topc(sK3)
% 2.10/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.10/1.01      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.10/1.01      inference(renaming,[status(thm)],[c_894]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1225,plain,
% 2.10/1.01      ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK3,X1_53,sK4,X0_53),sK6)
% 2.10/1.01      | r1_tmap_1(sK3,X1_53,sK4,sK6)
% 2.10/1.01      | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
% 2.10/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
% 2.10/1.01      | ~ m1_pre_topc(X0_53,sK3)
% 2.10/1.01      | v2_struct_0(X1_53)
% 2.10/1.01      | v2_struct_0(X0_53)
% 2.10/1.01      | ~ l1_pre_topc(X1_53)
% 2.10/1.01      | ~ l1_pre_topc(sK3)
% 2.10/1.01      | ~ v2_pre_topc(X1_53)
% 2.10/1.01      | ~ v2_pre_topc(sK3)
% 2.10/1.01      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 2.10/1.01      | u1_struct_0(X0_53) != u1_struct_0(sK2) ),
% 2.10/1.01      inference(subtyping,[status(esa)],[c_895]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1249,plain,
% 2.10/1.01      ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK3,X1_53,sK4,X0_53),sK6)
% 2.10/1.01      | r1_tmap_1(sK3,X1_53,sK4,sK6)
% 2.10/1.01      | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
% 2.10/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
% 2.10/1.01      | ~ m1_pre_topc(X0_53,sK3)
% 2.10/1.01      | v2_struct_0(X1_53)
% 2.10/1.01      | v2_struct_0(X0_53)
% 2.10/1.01      | ~ l1_pre_topc(X1_53)
% 2.10/1.01      | ~ v2_pre_topc(X1_53)
% 2.10/1.01      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 2.10/1.01      | u1_struct_0(X0_53) != u1_struct_0(sK2)
% 2.10/1.01      | ~ sP0_iProver_split ),
% 2.10/1.01      inference(splitting,
% 2.10/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.10/1.01                [c_1225]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1891,plain,
% 2.10/1.01      ( u1_struct_0(X0_53) != u1_struct_0(sK1)
% 2.10/1.01      | u1_struct_0(X1_53) != u1_struct_0(sK2)
% 2.10/1.01      | r1_tmap_1(X1_53,X0_53,k2_tmap_1(sK3,X0_53,sK4,X1_53),sK6) != iProver_top
% 2.10/1.01      | r1_tmap_1(sK3,X0_53,sK4,sK6) = iProver_top
% 2.10/1.01      | m1_subset_1(sK6,u1_struct_0(X1_53)) != iProver_top
% 2.10/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53)))) != iProver_top
% 2.10/1.01      | m1_pre_topc(X1_53,sK3) != iProver_top
% 2.10/1.01      | v2_struct_0(X0_53) = iProver_top
% 2.10/1.01      | v2_struct_0(X1_53) = iProver_top
% 2.10/1.01      | l1_pre_topc(X0_53) != iProver_top
% 2.10/1.01      | v2_pre_topc(X0_53) != iProver_top
% 2.10/1.01      | sP0_iProver_split != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1249]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1985,plain,
% 2.10/1.01      ( u1_struct_0(X0_53) != u1_struct_0(sK1)
% 2.10/1.01      | u1_struct_0(X1_53) != u1_struct_0(sK2)
% 2.10/1.01      | r1_tmap_1(X1_53,X0_53,k2_tmap_1(sK3,X0_53,sK4,X1_53),sK7) != iProver_top
% 2.10/1.01      | r1_tmap_1(sK3,X0_53,sK4,sK7) = iProver_top
% 2.10/1.01      | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
% 2.10/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53)))) != iProver_top
% 2.10/1.01      | m1_pre_topc(X1_53,sK3) != iProver_top
% 2.10/1.01      | v2_struct_0(X1_53) = iProver_top
% 2.10/1.01      | v2_struct_0(X0_53) = iProver_top
% 2.10/1.01      | l1_pre_topc(X0_53) != iProver_top
% 2.10/1.01      | v2_pre_topc(X0_53) != iProver_top
% 2.10/1.01      | sP0_iProver_split != iProver_top ),
% 2.10/1.01      inference(light_normalisation,[status(thm)],[c_1891,c_1244]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1250,plain,
% 2.10/1.01      ( ~ l1_pre_topc(sK3) | ~ v2_pre_topc(sK3) | sP0_iProver_split ),
% 2.10/1.01      inference(splitting,
% 2.10/1.01                [splitting(split),new_symbols(definition,[])],
% 2.10/1.01                [c_1225]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1303,plain,
% 2.10/1.01      ( l1_pre_topc(sK3) != iProver_top
% 2.10/1.01      | v2_pre_topc(sK3) != iProver_top
% 2.10/1.01      | sP0_iProver_split = iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1250]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2527,plain,
% 2.10/1.01      ( v2_pre_topc(X0_53) != iProver_top
% 2.10/1.01      | l1_pre_topc(X0_53) != iProver_top
% 2.10/1.01      | v2_struct_0(X0_53) = iProver_top
% 2.10/1.01      | v2_struct_0(X1_53) = iProver_top
% 2.10/1.01      | m1_pre_topc(X1_53,sK3) != iProver_top
% 2.10/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53)))) != iProver_top
% 2.10/1.01      | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
% 2.10/1.01      | r1_tmap_1(sK3,X0_53,sK4,sK7) = iProver_top
% 2.10/1.01      | r1_tmap_1(X1_53,X0_53,k2_tmap_1(sK3,X0_53,sK4,X1_53),sK7) != iProver_top
% 2.10/1.01      | u1_struct_0(X1_53) != u1_struct_0(sK2)
% 2.10/1.01      | u1_struct_0(X0_53) != u1_struct_0(sK1) ),
% 2.10/1.01      inference(global_propositional_subsumption,
% 2.10/1.01                [status(thm)],
% 2.10/1.01                [c_1985,c_31,c_32,c_39,c_1303,c_2200,c_2210]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2528,plain,
% 2.10/1.01      ( u1_struct_0(X0_53) != u1_struct_0(sK1)
% 2.10/1.01      | u1_struct_0(X1_53) != u1_struct_0(sK2)
% 2.10/1.01      | r1_tmap_1(X1_53,X0_53,k2_tmap_1(sK3,X0_53,sK4,X1_53),sK7) != iProver_top
% 2.10/1.01      | r1_tmap_1(sK3,X0_53,sK4,sK7) = iProver_top
% 2.10/1.01      | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
% 2.10/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53)))) != iProver_top
% 2.10/1.01      | m1_pre_topc(X1_53,sK3) != iProver_top
% 2.10/1.01      | v2_struct_0(X1_53) = iProver_top
% 2.10/1.01      | v2_struct_0(X0_53) = iProver_top
% 2.10/1.01      | l1_pre_topc(X0_53) != iProver_top
% 2.10/1.01      | v2_pre_topc(X0_53) != iProver_top ),
% 2.10/1.01      inference(renaming,[status(thm)],[c_2527]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2544,plain,
% 2.10/1.01      ( u1_struct_0(X0_53) != u1_struct_0(sK2)
% 2.10/1.01      | r1_tmap_1(X0_53,sK1,k2_tmap_1(sK3,sK1,sK4,X0_53),sK7) != iProver_top
% 2.10/1.01      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 2.10/1.01      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.10/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.10/1.01      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.10/1.01      | v2_struct_0(X0_53) = iProver_top
% 2.10/1.01      | v2_struct_0(sK1) = iProver_top
% 2.10/1.01      | l1_pre_topc(sK1) != iProver_top
% 2.10/1.01      | v2_pre_topc(sK1) != iProver_top ),
% 2.10/1.01      inference(equality_resolution,[status(thm)],[c_2528]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2854,plain,
% 2.10/1.01      ( v2_struct_0(X0_53) = iProver_top
% 2.10/1.01      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.10/1.01      | u1_struct_0(X0_53) != u1_struct_0(sK2)
% 2.10/1.01      | r1_tmap_1(X0_53,sK1,k2_tmap_1(sK3,sK1,sK4,X0_53),sK7) != iProver_top
% 2.10/1.01      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 2.10/1.01      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top ),
% 2.10/1.01      inference(global_propositional_subsumption,
% 2.10/1.01                [status(thm)],
% 2.10/1.01                [c_2544,c_33,c_34,c_35,c_42]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2855,plain,
% 2.10/1.01      ( u1_struct_0(X0_53) != u1_struct_0(sK2)
% 2.10/1.01      | r1_tmap_1(X0_53,sK1,k2_tmap_1(sK3,sK1,sK4,X0_53),sK7) != iProver_top
% 2.10/1.01      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 2.10/1.01      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.10/1.01      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.10/1.01      | v2_struct_0(X0_53) = iProver_top ),
% 2.10/1.01      inference(renaming,[status(thm)],[c_2854]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2866,plain,
% 2.10/1.01      ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 2.10/1.01      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top
% 2.10/1.01      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
% 2.10/1.01      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.10/1.01      | v2_struct_0(sK2) = iProver_top ),
% 2.10/1.01      inference(equality_resolution,[status(thm)],[c_2855]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_23,negated_conjecture,
% 2.10/1.01      ( ~ v2_struct_0(sK2) ),
% 2.10/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_36,plain,
% 2.10/1.01      ( v2_struct_0(sK2) != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_13,negated_conjecture,
% 2.10/1.01      ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
% 2.10/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_46,plain,
% 2.10/1.01      ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_3216,plain,
% 2.10/1.01      ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top
% 2.10/1.01      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top ),
% 2.10/1.01      inference(global_propositional_subsumption,
% 2.10/1.01                [status(thm)],
% 2.10/1.01                [c_2866,c_36,c_43,c_46]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_3217,plain,
% 2.10/1.01      ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 2.10/1.01      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top ),
% 2.10/1.01      inference(renaming,[status(thm)],[c_3216]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2338,plain,
% 2.10/1.01      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_1255]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1242,negated_conjecture,
% 2.10/1.01      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.10/1.01      inference(subtyping,[status(esa)],[c_14]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1873,plain,
% 2.10/1.01      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1242]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1920,plain,
% 2.10/1.01      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.10/1.01      inference(light_normalisation,[status(thm)],[c_1873,c_1244]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_7,negated_conjecture,
% 2.10/1.01      ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
% 2.10/1.01      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 2.10/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1246,negated_conjecture,
% 2.10/1.01      ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
% 2.10/1.01      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 2.10/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1870,plain,
% 2.10/1.01      ( r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top
% 2.10/1.01      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1246]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1950,plain,
% 2.10/1.01      ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 2.10/1.01      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
% 2.10/1.01      inference(light_normalisation,[status(thm)],[c_1870,c_1244]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_37,plain,
% 2.10/1.01      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(contradiction,plain,
% 2.10/1.01      ( $false ),
% 2.10/1.01      inference(minisat,
% 2.10/1.01                [status(thm)],
% 2.10/1.01                [c_3437,c_3307,c_3217,c_2338,c_2320,c_1920,c_1950,c_46,
% 2.10/1.01                 c_43,c_42,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,
% 2.10/1.01                 c_30]) ).
% 2.10/1.01  
% 2.10/1.01  
% 2.10/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.10/1.01  
% 2.10/1.01  ------                               Statistics
% 2.10/1.01  
% 2.10/1.01  ------ General
% 2.10/1.01  
% 2.10/1.01  abstr_ref_over_cycles:                  0
% 2.10/1.01  abstr_ref_under_cycles:                 0
% 2.10/1.01  gc_basic_clause_elim:                   0
% 2.10/1.01  forced_gc_time:                         0
% 2.10/1.01  parsing_time:                           0.01
% 2.10/1.01  unif_index_cands_time:                  0.
% 2.10/1.01  unif_index_add_time:                    0.
% 2.10/1.01  orderings_time:                         0.
% 2.10/1.01  out_proof_time:                         0.017
% 2.10/1.01  total_time:                             0.156
% 2.10/1.01  num_of_symbols:                         61
% 2.10/1.01  num_of_terms:                           2365
% 2.10/1.01  
% 2.10/1.01  ------ Preprocessing
% 2.10/1.01  
% 2.10/1.01  num_of_splits:                          2
% 2.10/1.01  num_of_split_atoms:                     2
% 2.10/1.01  num_of_reused_defs:                     0
% 2.10/1.01  num_eq_ax_congr_red:                    22
% 2.10/1.01  num_of_sem_filtered_clauses:            1
% 2.10/1.01  num_of_subtypes:                        3
% 2.10/1.01  monotx_restored_types:                  0
% 2.10/1.01  sat_num_of_epr_types:                   0
% 2.10/1.01  sat_num_of_non_cyclic_types:            0
% 2.10/1.01  sat_guarded_non_collapsed_types:        0
% 2.10/1.01  num_pure_diseq_elim:                    0
% 2.10/1.01  simp_replaced_by:                       0
% 2.10/1.01  res_preprocessed:                       132
% 2.10/1.01  prep_upred:                             0
% 2.10/1.01  prep_unflattend:                        11
% 2.10/1.01  smt_new_axioms:                         0
% 2.10/1.01  pred_elim_cands:                        6
% 2.10/1.01  pred_elim:                              5
% 2.10/1.01  pred_elim_cl:                           5
% 2.10/1.01  pred_elim_cycles:                       7
% 2.10/1.01  merged_defs:                            8
% 2.10/1.01  merged_defs_ncl:                        0
% 2.10/1.01  bin_hyper_res:                          8
% 2.10/1.01  prep_cycles:                            4
% 2.10/1.01  pred_elim_time:                         0.024
% 2.10/1.01  splitting_time:                         0.
% 2.10/1.01  sem_filter_time:                        0.
% 2.10/1.01  monotx_time:                            0.
% 2.10/1.01  subtype_inf_time:                       0.
% 2.10/1.01  
% 2.10/1.01  ------ Problem properties
% 2.10/1.01  
% 2.10/1.01  clauses:                                27
% 2.10/1.01  conjectures:                            18
% 2.10/1.01  epr:                                    16
% 2.10/1.01  horn:                                   21
% 2.10/1.01  ground:                                 20
% 2.10/1.01  unary:                                  16
% 2.10/1.01  binary:                                 2
% 2.10/1.01  lits:                                   99
% 2.10/1.01  lits_eq:                                13
% 2.10/1.01  fd_pure:                                0
% 2.10/1.01  fd_pseudo:                              0
% 2.10/1.01  fd_cond:                                0
% 2.10/1.01  fd_pseudo_cond:                         0
% 2.10/1.01  ac_symbols:                             0
% 2.10/1.01  
% 2.10/1.01  ------ Propositional Solver
% 2.10/1.01  
% 2.10/1.01  prop_solver_calls:                      27
% 2.10/1.01  prop_fast_solver_calls:                 1509
% 2.10/1.01  smt_solver_calls:                       0
% 2.10/1.01  smt_fast_solver_calls:                  0
% 2.10/1.01  prop_num_of_clauses:                    759
% 2.10/1.01  prop_preprocess_simplified:             3242
% 2.10/1.01  prop_fo_subsumed:                       64
% 2.10/1.01  prop_solver_time:                       0.
% 2.10/1.01  smt_solver_time:                        0.
% 2.10/1.01  smt_fast_solver_time:                   0.
% 2.10/1.01  prop_fast_solver_time:                  0.
% 2.10/1.01  prop_unsat_core_time:                   0.
% 2.10/1.01  
% 2.10/1.01  ------ QBF
% 2.10/1.01  
% 2.10/1.01  qbf_q_res:                              0
% 2.10/1.01  qbf_num_tautologies:                    0
% 2.10/1.01  qbf_prep_cycles:                        0
% 2.10/1.01  
% 2.10/1.01  ------ BMC1
% 2.10/1.01  
% 2.10/1.01  bmc1_current_bound:                     -1
% 2.10/1.01  bmc1_last_solved_bound:                 -1
% 2.10/1.01  bmc1_unsat_core_size:                   -1
% 2.10/1.01  bmc1_unsat_core_parents_size:           -1
% 2.10/1.01  bmc1_merge_next_fun:                    0
% 2.10/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.10/1.01  
% 2.10/1.01  ------ Instantiation
% 2.10/1.01  
% 2.10/1.01  inst_num_of_clauses:                    221
% 2.10/1.01  inst_num_in_passive:                    21
% 2.10/1.01  inst_num_in_active:                     183
% 2.10/1.01  inst_num_in_unprocessed:                17
% 2.10/1.01  inst_num_of_loops:                      220
% 2.10/1.01  inst_num_of_learning_restarts:          0
% 2.10/1.01  inst_num_moves_active_passive:          32
% 2.10/1.01  inst_lit_activity:                      0
% 2.10/1.01  inst_lit_activity_moves:                0
% 2.10/1.01  inst_num_tautologies:                   0
% 2.10/1.01  inst_num_prop_implied:                  0
% 2.10/1.01  inst_num_existing_simplified:           0
% 2.10/1.01  inst_num_eq_res_simplified:             0
% 2.10/1.01  inst_num_child_elim:                    0
% 2.10/1.01  inst_num_of_dismatching_blockings:      27
% 2.10/1.01  inst_num_of_non_proper_insts:           239
% 2.10/1.01  inst_num_of_duplicates:                 0
% 2.10/1.01  inst_inst_num_from_inst_to_res:         0
% 2.10/1.01  inst_dismatching_checking_time:         0.
% 2.10/1.01  
% 2.10/1.01  ------ Resolution
% 2.10/1.01  
% 2.10/1.01  res_num_of_clauses:                     0
% 2.10/1.01  res_num_in_passive:                     0
% 2.10/1.01  res_num_in_active:                      0
% 2.10/1.01  res_num_of_loops:                       136
% 2.10/1.01  res_forward_subset_subsumed:            59
% 2.10/1.01  res_backward_subset_subsumed:           2
% 2.10/1.01  res_forward_subsumed:                   0
% 2.10/1.01  res_backward_subsumed:                  0
% 2.10/1.01  res_forward_subsumption_resolution:     0
% 2.10/1.01  res_backward_subsumption_resolution:    0
% 2.10/1.01  res_clause_to_clause_subsumption:       201
% 2.10/1.01  res_orphan_elimination:                 0
% 2.10/1.01  res_tautology_del:                      63
% 2.10/1.01  res_num_eq_res_simplified:              0
% 2.10/1.01  res_num_sel_changes:                    0
% 2.10/1.01  res_moves_from_active_to_pass:          0
% 2.10/1.01  
% 2.10/1.01  ------ Superposition
% 2.10/1.01  
% 2.10/1.01  sup_time_total:                         0.
% 2.10/1.01  sup_time_generating:                    0.
% 2.10/1.01  sup_time_sim_full:                      0.
% 2.10/1.01  sup_time_sim_immed:                     0.
% 2.10/1.01  
% 2.10/1.01  sup_num_of_clauses:                     46
% 2.10/1.01  sup_num_in_active:                      41
% 2.10/1.01  sup_num_in_passive:                     5
% 2.10/1.01  sup_num_of_loops:                       43
% 2.10/1.01  sup_fw_superposition:                   9
% 2.10/1.01  sup_bw_superposition:                   3
% 2.10/1.01  sup_immediate_simplified:               2
% 2.10/1.01  sup_given_eliminated:                   0
% 2.10/1.01  comparisons_done:                       0
% 2.10/1.01  comparisons_avoided:                    0
% 2.10/1.01  
% 2.10/1.01  ------ Simplifications
% 2.10/1.01  
% 2.10/1.01  
% 2.10/1.01  sim_fw_subset_subsumed:                 0
% 2.10/1.01  sim_bw_subset_subsumed:                 0
% 2.10/1.01  sim_fw_subsumed:                        0
% 2.10/1.01  sim_bw_subsumed:                        0
% 2.10/1.01  sim_fw_subsumption_res:                 0
% 2.10/1.01  sim_bw_subsumption_res:                 0
% 2.10/1.01  sim_tautology_del:                      1
% 2.10/1.01  sim_eq_tautology_del:                   0
% 2.10/1.01  sim_eq_res_simp:                        0
% 2.10/1.01  sim_fw_demodulated:                     0
% 2.10/1.01  sim_bw_demodulated:                     2
% 2.10/1.01  sim_light_normalised:                   7
% 2.10/1.01  sim_joinable_taut:                      0
% 2.10/1.01  sim_joinable_simp:                      0
% 2.10/1.01  sim_ac_normalised:                      0
% 2.10/1.01  sim_smt_subsumption:                    0
% 2.10/1.01  
%------------------------------------------------------------------------------
