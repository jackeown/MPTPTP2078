%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:08 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 824 expanded)
%              Number of clauses        :  100 ( 131 expanded)
%              Number of leaves         :   16 ( 377 expanded)
%              Depth                    :   24
%              Number of atoms          : 1511 (18570 expanded)
%              Number of equality atoms :  406 (1351 expanded)
%              Maximal formula depth    :   31 (   9 average)
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

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(nnf_transformation,[],[f19])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f36,plain,(
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
     => ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8)
          | ~ r1_tmap_1(X3,X1,X4,X6) )
        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8)
          | r1_tmap_1(X3,X1,X4,X6) )
        & sK8 = X6
        & r1_tarski(X5,u1_struct_0(X2))
        & r2_hidden(X6,X5)
        & v3_pre_topc(X5,X3)
        & m1_subset_1(sK8,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
              | ~ r1_tmap_1(X3,X1,X4,sK7) )
            & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
              | r1_tmap_1(X3,X1,X4,sK7) )
            & sK7 = X7
            & r1_tarski(X5,u1_struct_0(X2))
            & r2_hidden(sK7,X5)
            & v3_pre_topc(X5,X3)
            & m1_subset_1(X7,u1_struct_0(X2)) )
        & m1_subset_1(sK7,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
                & r1_tarski(sK6,u1_struct_0(X2))
                & r2_hidden(X6,sK6)
                & v3_pre_topc(sK6,X3)
                & m1_subset_1(X7,u1_struct_0(X2)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
                    ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X7)
                      | ~ r1_tmap_1(X3,X1,sK5,X6) )
                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X7)
                      | r1_tmap_1(X3,X1,sK5,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(X2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,X3)
                    & m1_subset_1(X7,u1_struct_0(X2)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
                        ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X7)
                          | ~ r1_tmap_1(sK4,X1,X4,X6) )
                        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X7)
                          | r1_tmap_1(sK4,X1,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(X2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,sK4)
                        & m1_subset_1(X7,u1_struct_0(X2)) )
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK4))) )
            & m1_pre_topc(X2,sK4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
                            ( ( ~ r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X7)
                              | ~ r1_tmap_1(X3,X1,X4,X6) )
                            & ( r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X7)
                              | r1_tmap_1(X3,X1,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(sK3))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,X3)
                            & m1_subset_1(X7,u1_struct_0(sK3)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                & m1_pre_topc(sK3,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
                                ( ( ~ r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,sK2,X4,X6) )
                                & ( r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,sK2,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,X3)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
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

fof(f29,plain,
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
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X7)
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
    ( ( ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
      | ~ r1_tmap_1(sK4,sK2,sK5,sK7) )
    & ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
      | r1_tmap_1(sK4,sK2,sK5,sK7) )
    & sK7 = sK8
    & r1_tarski(sK6,u1_struct_0(sK3))
    & r2_hidden(sK7,sK6)
    & v3_pre_topc(sK6,sK4)
    & m1_subset_1(sK8,u1_struct_0(sK3))
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f28,f36,f35,f34,f33,f32,f31,f30,f29])).

fof(f66,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK0(X0,X1,X2))
        & r1_tarski(sK0(X0,X1,X2),X2)
        & v3_pre_topc(sK0(X0,X1,X2),X0)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK0(X0,X1,X2))
                    & r1_tarski(sK0(X0,X1,X2),X2)
                    & v3_pre_topc(sK0(X0,X1,X2),X0)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f68,plain,(
    v3_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f72,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
    | r1_tmap_1(sK4,sK2,sK5,sK7) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f16])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X1,X4,X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) ) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(nnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f50])).

fof(f62,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X6)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f49])).

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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f15])).

fof(f76,plain,(
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
    inference(equality_resolution,[],[f48])).

fof(f73,plain,
    ( ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
    | ~ r1_tmap_1(sK4,sK2,sK5,sK7) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2504,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_15,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2551,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2504,c_15])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2503,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2515,plain,
    ( m1_connsp_2(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | v3_pre_topc(X3,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r1_tarski(X3,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4601,plain,
    ( m1_connsp_2(sK6,sK4,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v3_pre_topc(X1,sK4) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,sK6) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2503,c_2515])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_37,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_38,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_44,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_45,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2849,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2850,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2849])).

cnf(c_2852,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2850])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2883,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2884,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2883])).

cnf(c_2886,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2884])).

cnf(c_4706,plain,
    ( r1_tarski(X1,sK6) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v3_pre_topc(X1,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_connsp_2(sK6,sK4,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4601,c_37,c_38,c_44,c_45,c_2852,c_2886])).

cnf(c_4707,plain,
    ( m1_connsp_2(sK6,sK4,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v3_pre_topc(X1,sK4) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_4706])).

cnf(c_4719,plain,
    ( m1_connsp_2(sK6,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v3_pre_topc(sK6,sK4) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2503,c_4707])).

cnf(c_18,negated_conjecture,
    ( v3_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_53,plain,
    ( v3_pre_topc(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3702,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3705,plain,
    ( r1_tarski(sK6,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3702])).

cnf(c_4759,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | m1_connsp_2(sK6,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4719,c_53,c_3705])).

cnf(c_4760,plain,
    ( m1_connsp_2(sK6,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_4759])).

cnf(c_4768,plain,
    ( m1_connsp_2(sK6,sK4,sK8) = iProver_top
    | r2_hidden(sK8,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2551,c_4760])).

cnf(c_14,negated_conjecture,
    ( r1_tmap_1(sK4,sK2,sK5,sK7)
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2509,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2574,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8) = iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2509,c_15])).

cnf(c_11,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_667,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_668,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_667])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_672,plain,
    ( ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_connsp_2(X5,X3,X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_668,c_25])).

cnf(c_673,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_672])).

cnf(c_2489,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) != iProver_top
    | r1_tmap_1(X0,X1,sK5,X4) = iProver_top
    | m1_connsp_2(X5,X0,X4) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X3) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | r1_tarski(X5,u1_struct_0(X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_3014,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
    | m1_connsp_2(X4,sK4,X3) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2489])).

cnf(c_3877,plain,
    ( v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_connsp_2(X4,sK4,X3) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3014,c_44])).

cnf(c_3878,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
    | m1_connsp_2(X4,sK4,X3) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3877])).

cnf(c_3900,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | m1_connsp_2(X3,sK4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3878])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_39,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_40,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_41,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_48,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4374,plain,
    ( v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | m1_connsp_2(X3,sK4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3900,c_39,c_40,c_41,c_48])).

cnf(c_4375,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | m1_connsp_2(X3,sK4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4374])).

cnf(c_4394,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8) = iProver_top
    | m1_connsp_2(X0,sK4,sK8) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2574,c_4375])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_36,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_42,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_43,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_49,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_52,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_12,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_10,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_184,plain,
    ( ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_10])).

cnf(c_185,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(renaming,[status(thm)],[c_184])).

cnf(c_601,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_185,c_24])).

cnf(c_602,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_606,plain,
    ( ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_602,c_25])).

cnf(c_607,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_606])).

cnf(c_2490,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) = iProver_top
    | r1_tmap_1(X0,X1,sK5,X4) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X3) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_3358,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2490])).

cnf(c_3838,plain,
    ( v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3358,c_44])).

cnf(c_3839,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3838])).

cnf(c_3858,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3839])).

cnf(c_3905,plain,
    ( v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3858,c_39,c_40,c_41,c_48])).

cnf(c_3906,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3905])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK7)
    | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2510,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2579,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2510,c_15])).

cnf(c_3922,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3906,c_2579])).

cnf(c_4426,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_connsp_2(X0,sK4,sK8) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4394,c_36,c_37,c_38,c_42,c_43,c_45,c_49,c_52,c_2551,c_3922])).

cnf(c_4427,plain,
    ( m1_connsp_2(X0,sK4,sK8) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4426])).

cnf(c_4436,plain,
    ( m1_connsp_2(sK6,sK4,sK8) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2503,c_4427])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2507,plain,
    ( r2_hidden(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2546,plain,
    ( r2_hidden(sK8,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2507,c_15])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_55,plain,
    ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4768,c_4436,c_2546,c_55])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:48:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.96/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.00  
% 1.96/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.96/1.00  
% 1.96/1.00  ------  iProver source info
% 1.96/1.00  
% 1.96/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.96/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.96/1.00  git: non_committed_changes: false
% 1.96/1.00  git: last_make_outside_of_git: false
% 1.96/1.00  
% 1.96/1.00  ------ 
% 1.96/1.00  
% 1.96/1.00  ------ Input Options
% 1.96/1.00  
% 1.96/1.00  --out_options                           all
% 1.96/1.00  --tptp_safe_out                         true
% 1.96/1.00  --problem_path                          ""
% 1.96/1.00  --include_path                          ""
% 1.96/1.00  --clausifier                            res/vclausify_rel
% 1.96/1.00  --clausifier_options                    --mode clausify
% 1.96/1.00  --stdin                                 false
% 1.96/1.00  --stats_out                             all
% 1.96/1.00  
% 1.96/1.00  ------ General Options
% 1.96/1.00  
% 1.96/1.00  --fof                                   false
% 1.96/1.00  --time_out_real                         305.
% 1.96/1.00  --time_out_virtual                      -1.
% 1.96/1.00  --symbol_type_check                     false
% 1.96/1.00  --clausify_out                          false
% 1.96/1.00  --sig_cnt_out                           false
% 1.96/1.00  --trig_cnt_out                          false
% 1.96/1.00  --trig_cnt_out_tolerance                1.
% 1.96/1.00  --trig_cnt_out_sk_spl                   false
% 1.96/1.00  --abstr_cl_out                          false
% 1.96/1.00  
% 1.96/1.00  ------ Global Options
% 1.96/1.00  
% 1.96/1.00  --schedule                              default
% 1.96/1.00  --add_important_lit                     false
% 1.96/1.00  --prop_solver_per_cl                    1000
% 1.96/1.00  --min_unsat_core                        false
% 1.96/1.00  --soft_assumptions                      false
% 1.96/1.00  --soft_lemma_size                       3
% 1.96/1.00  --prop_impl_unit_size                   0
% 1.96/1.00  --prop_impl_unit                        []
% 1.96/1.00  --share_sel_clauses                     true
% 1.96/1.00  --reset_solvers                         false
% 1.96/1.00  --bc_imp_inh                            [conj_cone]
% 1.96/1.00  --conj_cone_tolerance                   3.
% 1.96/1.00  --extra_neg_conj                        none
% 1.96/1.00  --large_theory_mode                     true
% 1.96/1.00  --prolific_symb_bound                   200
% 1.96/1.00  --lt_threshold                          2000
% 1.96/1.00  --clause_weak_htbl                      true
% 1.96/1.00  --gc_record_bc_elim                     false
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing Options
% 1.96/1.00  
% 1.96/1.00  --preprocessing_flag                    true
% 1.96/1.00  --time_out_prep_mult                    0.1
% 1.96/1.00  --splitting_mode                        input
% 1.96/1.00  --splitting_grd                         true
% 1.96/1.00  --splitting_cvd                         false
% 1.96/1.00  --splitting_cvd_svl                     false
% 1.96/1.00  --splitting_nvd                         32
% 1.96/1.00  --sub_typing                            true
% 1.96/1.00  --prep_gs_sim                           true
% 1.96/1.00  --prep_unflatten                        true
% 1.96/1.00  --prep_res_sim                          true
% 1.96/1.00  --prep_upred                            true
% 1.96/1.00  --prep_sem_filter                       exhaustive
% 1.96/1.00  --prep_sem_filter_out                   false
% 1.96/1.00  --pred_elim                             true
% 1.96/1.00  --res_sim_input                         true
% 1.96/1.00  --eq_ax_congr_red                       true
% 1.96/1.00  --pure_diseq_elim                       true
% 1.96/1.00  --brand_transform                       false
% 1.96/1.00  --non_eq_to_eq                          false
% 1.96/1.00  --prep_def_merge                        true
% 1.96/1.00  --prep_def_merge_prop_impl              false
% 1.96/1.00  --prep_def_merge_mbd                    true
% 1.96/1.00  --prep_def_merge_tr_red                 false
% 1.96/1.00  --prep_def_merge_tr_cl                  false
% 1.96/1.00  --smt_preprocessing                     true
% 1.96/1.00  --smt_ac_axioms                         fast
% 1.96/1.00  --preprocessed_out                      false
% 1.96/1.00  --preprocessed_stats                    false
% 1.96/1.00  
% 1.96/1.00  ------ Abstraction refinement Options
% 1.96/1.00  
% 1.96/1.00  --abstr_ref                             []
% 1.96/1.00  --abstr_ref_prep                        false
% 1.96/1.00  --abstr_ref_until_sat                   false
% 1.96/1.00  --abstr_ref_sig_restrict                funpre
% 1.96/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/1.00  --abstr_ref_under                       []
% 1.96/1.00  
% 1.96/1.00  ------ SAT Options
% 1.96/1.00  
% 1.96/1.00  --sat_mode                              false
% 1.96/1.00  --sat_fm_restart_options                ""
% 1.96/1.00  --sat_gr_def                            false
% 1.96/1.00  --sat_epr_types                         true
% 1.96/1.00  --sat_non_cyclic_types                  false
% 1.96/1.00  --sat_finite_models                     false
% 1.96/1.00  --sat_fm_lemmas                         false
% 1.96/1.00  --sat_fm_prep                           false
% 1.96/1.00  --sat_fm_uc_incr                        true
% 1.96/1.00  --sat_out_model                         small
% 1.96/1.00  --sat_out_clauses                       false
% 1.96/1.00  
% 1.96/1.00  ------ QBF Options
% 1.96/1.00  
% 1.96/1.00  --qbf_mode                              false
% 1.96/1.00  --qbf_elim_univ                         false
% 1.96/1.00  --qbf_dom_inst                          none
% 1.96/1.00  --qbf_dom_pre_inst                      false
% 1.96/1.00  --qbf_sk_in                             false
% 1.96/1.00  --qbf_pred_elim                         true
% 1.96/1.00  --qbf_split                             512
% 1.96/1.00  
% 1.96/1.00  ------ BMC1 Options
% 1.96/1.00  
% 1.96/1.00  --bmc1_incremental                      false
% 1.96/1.00  --bmc1_axioms                           reachable_all
% 1.96/1.00  --bmc1_min_bound                        0
% 1.96/1.00  --bmc1_max_bound                        -1
% 1.96/1.00  --bmc1_max_bound_default                -1
% 1.96/1.00  --bmc1_symbol_reachability              true
% 1.96/1.00  --bmc1_property_lemmas                  false
% 1.96/1.00  --bmc1_k_induction                      false
% 1.96/1.00  --bmc1_non_equiv_states                 false
% 1.96/1.00  --bmc1_deadlock                         false
% 1.96/1.00  --bmc1_ucm                              false
% 1.96/1.00  --bmc1_add_unsat_core                   none
% 1.96/1.00  --bmc1_unsat_core_children              false
% 1.96/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/1.00  --bmc1_out_stat                         full
% 1.96/1.00  --bmc1_ground_init                      false
% 1.96/1.00  --bmc1_pre_inst_next_state              false
% 1.96/1.00  --bmc1_pre_inst_state                   false
% 1.96/1.00  --bmc1_pre_inst_reach_state             false
% 1.96/1.00  --bmc1_out_unsat_core                   false
% 1.96/1.00  --bmc1_aig_witness_out                  false
% 1.96/1.00  --bmc1_verbose                          false
% 1.96/1.00  --bmc1_dump_clauses_tptp                false
% 1.96/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.96/1.00  --bmc1_dump_file                        -
% 1.96/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.96/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.96/1.00  --bmc1_ucm_extend_mode                  1
% 1.96/1.00  --bmc1_ucm_init_mode                    2
% 1.96/1.00  --bmc1_ucm_cone_mode                    none
% 1.96/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.96/1.00  --bmc1_ucm_relax_model                  4
% 1.96/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.96/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/1.00  --bmc1_ucm_layered_model                none
% 1.96/1.00  --bmc1_ucm_max_lemma_size               10
% 1.96/1.00  
% 1.96/1.00  ------ AIG Options
% 1.96/1.00  
% 1.96/1.00  --aig_mode                              false
% 1.96/1.00  
% 1.96/1.00  ------ Instantiation Options
% 1.96/1.00  
% 1.96/1.00  --instantiation_flag                    true
% 1.96/1.00  --inst_sos_flag                         false
% 1.96/1.00  --inst_sos_phase                        true
% 1.96/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel_side                     num_symb
% 1.96/1.00  --inst_solver_per_active                1400
% 1.96/1.00  --inst_solver_calls_frac                1.
% 1.96/1.00  --inst_passive_queue_type               priority_queues
% 1.96/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/1.00  --inst_passive_queues_freq              [25;2]
% 1.96/1.00  --inst_dismatching                      true
% 1.96/1.00  --inst_eager_unprocessed_to_passive     true
% 1.96/1.00  --inst_prop_sim_given                   true
% 1.96/1.00  --inst_prop_sim_new                     false
% 1.96/1.00  --inst_subs_new                         false
% 1.96/1.00  --inst_eq_res_simp                      false
% 1.96/1.00  --inst_subs_given                       false
% 1.96/1.00  --inst_orphan_elimination               true
% 1.96/1.00  --inst_learning_loop_flag               true
% 1.96/1.00  --inst_learning_start                   3000
% 1.96/1.00  --inst_learning_factor                  2
% 1.96/1.00  --inst_start_prop_sim_after_learn       3
% 1.96/1.00  --inst_sel_renew                        solver
% 1.96/1.00  --inst_lit_activity_flag                true
% 1.96/1.00  --inst_restr_to_given                   false
% 1.96/1.00  --inst_activity_threshold               500
% 1.96/1.00  --inst_out_proof                        true
% 1.96/1.00  
% 1.96/1.00  ------ Resolution Options
% 1.96/1.00  
% 1.96/1.00  --resolution_flag                       true
% 1.96/1.00  --res_lit_sel                           adaptive
% 1.96/1.00  --res_lit_sel_side                      none
% 1.96/1.00  --res_ordering                          kbo
% 1.96/1.00  --res_to_prop_solver                    active
% 1.96/1.00  --res_prop_simpl_new                    false
% 1.96/1.00  --res_prop_simpl_given                  true
% 1.96/1.00  --res_passive_queue_type                priority_queues
% 1.96/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/1.00  --res_passive_queues_freq               [15;5]
% 1.96/1.00  --res_forward_subs                      full
% 1.96/1.00  --res_backward_subs                     full
% 1.96/1.00  --res_forward_subs_resolution           true
% 1.96/1.00  --res_backward_subs_resolution          true
% 1.96/1.00  --res_orphan_elimination                true
% 1.96/1.00  --res_time_limit                        2.
% 1.96/1.00  --res_out_proof                         true
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Options
% 1.96/1.00  
% 1.96/1.00  --superposition_flag                    true
% 1.96/1.00  --sup_passive_queue_type                priority_queues
% 1.96/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.96/1.00  --demod_completeness_check              fast
% 1.96/1.00  --demod_use_ground                      true
% 1.96/1.00  --sup_to_prop_solver                    passive
% 1.96/1.00  --sup_prop_simpl_new                    true
% 1.96/1.00  --sup_prop_simpl_given                  true
% 1.96/1.00  --sup_fun_splitting                     false
% 1.96/1.00  --sup_smt_interval                      50000
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Simplification Setup
% 1.96/1.00  
% 1.96/1.00  --sup_indices_passive                   []
% 1.96/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_full_bw                           [BwDemod]
% 1.96/1.00  --sup_immed_triv                        [TrivRules]
% 1.96/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_immed_bw_main                     []
% 1.96/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  
% 1.96/1.00  ------ Combination Options
% 1.96/1.00  
% 1.96/1.00  --comb_res_mult                         3
% 1.96/1.00  --comb_sup_mult                         2
% 1.96/1.00  --comb_inst_mult                        10
% 1.96/1.00  
% 1.96/1.00  ------ Debug Options
% 1.96/1.00  
% 1.96/1.00  --dbg_backtrace                         false
% 1.96/1.00  --dbg_dump_prop_clauses                 false
% 1.96/1.00  --dbg_dump_prop_clauses_file            -
% 1.96/1.00  --dbg_out_stat                          false
% 1.96/1.00  ------ Parsing...
% 1.96/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.96/1.00  ------ Proving...
% 1.96/1.00  ------ Problem Properties 
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  clauses                                 32
% 1.96/1.00  conjectures                             21
% 1.96/1.00  EPR                                     18
% 1.96/1.00  Horn                                    24
% 1.96/1.00  unary                                   20
% 1.96/1.00  binary                                  2
% 1.96/1.00  lits                                    111
% 1.96/1.00  lits eq                                 6
% 1.96/1.00  fd_pure                                 0
% 1.96/1.00  fd_pseudo                               0
% 1.96/1.00  fd_cond                                 0
% 1.96/1.00  fd_pseudo_cond                          1
% 1.96/1.00  AC symbols                              0
% 1.96/1.00  
% 1.96/1.00  ------ Schedule dynamic 5 is on 
% 1.96/1.00  
% 1.96/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  ------ 
% 1.96/1.00  Current options:
% 1.96/1.00  ------ 
% 1.96/1.00  
% 1.96/1.00  ------ Input Options
% 1.96/1.00  
% 1.96/1.00  --out_options                           all
% 1.96/1.00  --tptp_safe_out                         true
% 1.96/1.00  --problem_path                          ""
% 1.96/1.00  --include_path                          ""
% 1.96/1.00  --clausifier                            res/vclausify_rel
% 1.96/1.00  --clausifier_options                    --mode clausify
% 1.96/1.00  --stdin                                 false
% 1.96/1.00  --stats_out                             all
% 1.96/1.00  
% 1.96/1.00  ------ General Options
% 1.96/1.00  
% 1.96/1.00  --fof                                   false
% 1.96/1.00  --time_out_real                         305.
% 1.96/1.00  --time_out_virtual                      -1.
% 1.96/1.00  --symbol_type_check                     false
% 1.96/1.00  --clausify_out                          false
% 1.96/1.00  --sig_cnt_out                           false
% 1.96/1.00  --trig_cnt_out                          false
% 1.96/1.00  --trig_cnt_out_tolerance                1.
% 1.96/1.00  --trig_cnt_out_sk_spl                   false
% 1.96/1.00  --abstr_cl_out                          false
% 1.96/1.00  
% 1.96/1.00  ------ Global Options
% 1.96/1.00  
% 1.96/1.00  --schedule                              default
% 1.96/1.00  --add_important_lit                     false
% 1.96/1.00  --prop_solver_per_cl                    1000
% 1.96/1.00  --min_unsat_core                        false
% 1.96/1.00  --soft_assumptions                      false
% 1.96/1.00  --soft_lemma_size                       3
% 1.96/1.00  --prop_impl_unit_size                   0
% 1.96/1.00  --prop_impl_unit                        []
% 1.96/1.00  --share_sel_clauses                     true
% 1.96/1.00  --reset_solvers                         false
% 1.96/1.00  --bc_imp_inh                            [conj_cone]
% 1.96/1.00  --conj_cone_tolerance                   3.
% 1.96/1.00  --extra_neg_conj                        none
% 1.96/1.00  --large_theory_mode                     true
% 1.96/1.00  --prolific_symb_bound                   200
% 1.96/1.00  --lt_threshold                          2000
% 1.96/1.00  --clause_weak_htbl                      true
% 1.96/1.00  --gc_record_bc_elim                     false
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing Options
% 1.96/1.00  
% 1.96/1.00  --preprocessing_flag                    true
% 1.96/1.00  --time_out_prep_mult                    0.1
% 1.96/1.00  --splitting_mode                        input
% 1.96/1.00  --splitting_grd                         true
% 1.96/1.00  --splitting_cvd                         false
% 1.96/1.00  --splitting_cvd_svl                     false
% 1.96/1.00  --splitting_nvd                         32
% 1.96/1.00  --sub_typing                            true
% 1.96/1.00  --prep_gs_sim                           true
% 1.96/1.00  --prep_unflatten                        true
% 1.96/1.00  --prep_res_sim                          true
% 1.96/1.00  --prep_upred                            true
% 1.96/1.00  --prep_sem_filter                       exhaustive
% 1.96/1.00  --prep_sem_filter_out                   false
% 1.96/1.00  --pred_elim                             true
% 1.96/1.00  --res_sim_input                         true
% 1.96/1.00  --eq_ax_congr_red                       true
% 1.96/1.00  --pure_diseq_elim                       true
% 1.96/1.00  --brand_transform                       false
% 1.96/1.00  --non_eq_to_eq                          false
% 1.96/1.00  --prep_def_merge                        true
% 1.96/1.00  --prep_def_merge_prop_impl              false
% 1.96/1.00  --prep_def_merge_mbd                    true
% 1.96/1.00  --prep_def_merge_tr_red                 false
% 1.96/1.00  --prep_def_merge_tr_cl                  false
% 1.96/1.00  --smt_preprocessing                     true
% 1.96/1.00  --smt_ac_axioms                         fast
% 1.96/1.00  --preprocessed_out                      false
% 1.96/1.00  --preprocessed_stats                    false
% 1.96/1.00  
% 1.96/1.00  ------ Abstraction refinement Options
% 1.96/1.00  
% 1.96/1.00  --abstr_ref                             []
% 1.96/1.00  --abstr_ref_prep                        false
% 1.96/1.00  --abstr_ref_until_sat                   false
% 1.96/1.00  --abstr_ref_sig_restrict                funpre
% 1.96/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/1.00  --abstr_ref_under                       []
% 1.96/1.00  
% 1.96/1.00  ------ SAT Options
% 1.96/1.00  
% 1.96/1.00  --sat_mode                              false
% 1.96/1.00  --sat_fm_restart_options                ""
% 1.96/1.00  --sat_gr_def                            false
% 1.96/1.00  --sat_epr_types                         true
% 1.96/1.00  --sat_non_cyclic_types                  false
% 1.96/1.00  --sat_finite_models                     false
% 1.96/1.00  --sat_fm_lemmas                         false
% 1.96/1.00  --sat_fm_prep                           false
% 1.96/1.00  --sat_fm_uc_incr                        true
% 1.96/1.00  --sat_out_model                         small
% 1.96/1.00  --sat_out_clauses                       false
% 1.96/1.00  
% 1.96/1.00  ------ QBF Options
% 1.96/1.00  
% 1.96/1.00  --qbf_mode                              false
% 1.96/1.00  --qbf_elim_univ                         false
% 1.96/1.00  --qbf_dom_inst                          none
% 1.96/1.00  --qbf_dom_pre_inst                      false
% 1.96/1.00  --qbf_sk_in                             false
% 1.96/1.00  --qbf_pred_elim                         true
% 1.96/1.00  --qbf_split                             512
% 1.96/1.00  
% 1.96/1.00  ------ BMC1 Options
% 1.96/1.00  
% 1.96/1.00  --bmc1_incremental                      false
% 1.96/1.00  --bmc1_axioms                           reachable_all
% 1.96/1.00  --bmc1_min_bound                        0
% 1.96/1.00  --bmc1_max_bound                        -1
% 1.96/1.00  --bmc1_max_bound_default                -1
% 1.96/1.00  --bmc1_symbol_reachability              true
% 1.96/1.00  --bmc1_property_lemmas                  false
% 1.96/1.00  --bmc1_k_induction                      false
% 1.96/1.00  --bmc1_non_equiv_states                 false
% 1.96/1.00  --bmc1_deadlock                         false
% 1.96/1.00  --bmc1_ucm                              false
% 1.96/1.00  --bmc1_add_unsat_core                   none
% 1.96/1.00  --bmc1_unsat_core_children              false
% 1.96/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/1.00  --bmc1_out_stat                         full
% 1.96/1.00  --bmc1_ground_init                      false
% 1.96/1.00  --bmc1_pre_inst_next_state              false
% 1.96/1.00  --bmc1_pre_inst_state                   false
% 1.96/1.00  --bmc1_pre_inst_reach_state             false
% 1.96/1.00  --bmc1_out_unsat_core                   false
% 1.96/1.00  --bmc1_aig_witness_out                  false
% 1.96/1.00  --bmc1_verbose                          false
% 1.96/1.00  --bmc1_dump_clauses_tptp                false
% 1.96/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.96/1.00  --bmc1_dump_file                        -
% 1.96/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.96/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.96/1.00  --bmc1_ucm_extend_mode                  1
% 1.96/1.00  --bmc1_ucm_init_mode                    2
% 1.96/1.00  --bmc1_ucm_cone_mode                    none
% 1.96/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.96/1.00  --bmc1_ucm_relax_model                  4
% 1.96/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.96/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/1.00  --bmc1_ucm_layered_model                none
% 1.96/1.00  --bmc1_ucm_max_lemma_size               10
% 1.96/1.00  
% 1.96/1.00  ------ AIG Options
% 1.96/1.00  
% 1.96/1.00  --aig_mode                              false
% 1.96/1.00  
% 1.96/1.00  ------ Instantiation Options
% 1.96/1.00  
% 1.96/1.00  --instantiation_flag                    true
% 1.96/1.00  --inst_sos_flag                         false
% 1.96/1.00  --inst_sos_phase                        true
% 1.96/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel_side                     none
% 1.96/1.00  --inst_solver_per_active                1400
% 1.96/1.00  --inst_solver_calls_frac                1.
% 1.96/1.00  --inst_passive_queue_type               priority_queues
% 1.96/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/1.00  --inst_passive_queues_freq              [25;2]
% 1.96/1.00  --inst_dismatching                      true
% 1.96/1.00  --inst_eager_unprocessed_to_passive     true
% 1.96/1.00  --inst_prop_sim_given                   true
% 1.96/1.00  --inst_prop_sim_new                     false
% 1.96/1.00  --inst_subs_new                         false
% 1.96/1.00  --inst_eq_res_simp                      false
% 1.96/1.00  --inst_subs_given                       false
% 1.96/1.00  --inst_orphan_elimination               true
% 1.96/1.00  --inst_learning_loop_flag               true
% 1.96/1.00  --inst_learning_start                   3000
% 1.96/1.00  --inst_learning_factor                  2
% 1.96/1.00  --inst_start_prop_sim_after_learn       3
% 1.96/1.00  --inst_sel_renew                        solver
% 1.96/1.00  --inst_lit_activity_flag                true
% 1.96/1.00  --inst_restr_to_given                   false
% 1.96/1.00  --inst_activity_threshold               500
% 1.96/1.00  --inst_out_proof                        true
% 1.96/1.00  
% 1.96/1.00  ------ Resolution Options
% 1.96/1.00  
% 1.96/1.00  --resolution_flag                       false
% 1.96/1.00  --res_lit_sel                           adaptive
% 1.96/1.00  --res_lit_sel_side                      none
% 1.96/1.00  --res_ordering                          kbo
% 1.96/1.00  --res_to_prop_solver                    active
% 1.96/1.00  --res_prop_simpl_new                    false
% 1.96/1.00  --res_prop_simpl_given                  true
% 1.96/1.00  --res_passive_queue_type                priority_queues
% 1.96/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/1.00  --res_passive_queues_freq               [15;5]
% 1.96/1.00  --res_forward_subs                      full
% 1.96/1.00  --res_backward_subs                     full
% 1.96/1.00  --res_forward_subs_resolution           true
% 1.96/1.00  --res_backward_subs_resolution          true
% 1.96/1.00  --res_orphan_elimination                true
% 1.96/1.00  --res_time_limit                        2.
% 1.96/1.00  --res_out_proof                         true
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Options
% 1.96/1.00  
% 1.96/1.00  --superposition_flag                    true
% 1.96/1.00  --sup_passive_queue_type                priority_queues
% 1.96/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.96/1.00  --demod_completeness_check              fast
% 1.96/1.00  --demod_use_ground                      true
% 1.96/1.00  --sup_to_prop_solver                    passive
% 1.96/1.00  --sup_prop_simpl_new                    true
% 1.96/1.00  --sup_prop_simpl_given                  true
% 1.96/1.00  --sup_fun_splitting                     false
% 1.96/1.00  --sup_smt_interval                      50000
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Simplification Setup
% 1.96/1.00  
% 1.96/1.00  --sup_indices_passive                   []
% 1.96/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_full_bw                           [BwDemod]
% 1.96/1.00  --sup_immed_triv                        [TrivRules]
% 1.96/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_immed_bw_main                     []
% 1.96/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  
% 1.96/1.00  ------ Combination Options
% 1.96/1.00  
% 1.96/1.00  --comb_res_mult                         3
% 1.96/1.00  --comb_sup_mult                         2
% 1.96/1.00  --comb_inst_mult                        10
% 1.96/1.00  
% 1.96/1.00  ------ Debug Options
% 1.96/1.00  
% 1.96/1.00  --dbg_backtrace                         false
% 1.96/1.00  --dbg_dump_prop_clauses                 false
% 1.96/1.00  --dbg_dump_prop_clauses_file            -
% 1.96/1.00  --dbg_out_stat                          false
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  ------ Proving...
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  % SZS status Theorem for theBenchmark.p
% 1.96/1.00  
% 1.96/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.96/1.00  
% 1.96/1.00  fof(f7,conjecture,(
% 1.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f8,negated_conjecture,(
% 1.96/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.96/1.00    inference(negated_conjecture,[],[f7])).
% 1.96/1.00  
% 1.96/1.00  fof(f18,plain,(
% 1.96/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f8])).
% 1.96/1.00  
% 1.96/1.00  fof(f19,plain,(
% 1.96/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f18])).
% 1.96/1.00  
% 1.96/1.00  fof(f27,plain,(
% 1.96/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.96/1.00    inference(nnf_transformation,[],[f19])).
% 1.96/1.00  
% 1.96/1.00  fof(f28,plain,(
% 1.96/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f27])).
% 1.96/1.00  
% 1.96/1.00  fof(f36,plain,(
% 1.96/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8) | r1_tmap_1(X3,X1,X4,X6)) & sK8 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(sK8,u1_struct_0(X2)))) )),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f35,plain,(
% 1.96/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,sK7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,sK7)) & sK7 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK7,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f34,plain,(
% 1.96/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(sK6,u1_struct_0(X2)) & r2_hidden(X6,sK6) & v3_pre_topc(sK6,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X3))))) )),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f33,plain,(
% 1.96/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X7) | ~r1_tmap_1(X3,X1,sK5,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X7) | r1_tmap_1(X3,X1,sK5,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f32,plain,(
% 1.96/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X7) | ~r1_tmap_1(sK4,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X7) | r1_tmap_1(sK4,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK4) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_pre_topc(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f31,plain,(
% 1.96/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK3)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(sK3))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f30,plain,(
% 1.96/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK2,X4,X6)) & (r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X7) | r1_tmap_1(X3,sK2,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f29,plain,(
% 1.96/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f37,plain,(
% 1.96/1.00    ((((((((~r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK2,sK5,sK7)) & (r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK2,sK5,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK3)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK4) & m1_subset_1(sK8,u1_struct_0(sK3))) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_pre_topc(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f28,f36,f35,f34,f33,f32,f31,f30,f29])).
% 1.96/1.00  
% 1.96/1.00  fof(f66,plain,(
% 1.96/1.00    m1_subset_1(sK7,u1_struct_0(sK4))),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f71,plain,(
% 1.96/1.00    sK7 = sK8),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f65,plain,(
% 1.96/1.00    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f4,axiom,(
% 1.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f12,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f4])).
% 1.96/1.00  
% 1.96/1.00  fof(f13,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f12])).
% 1.96/1.00  
% 1.96/1.00  fof(f22,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(nnf_transformation,[],[f13])).
% 1.96/1.00  
% 1.96/1.00  fof(f23,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(rectify,[],[f22])).
% 1.96/1.00  
% 1.96/1.00  fof(f24,plain,(
% 1.96/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK0(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f25,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK0(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 1.96/1.00  
% 1.96/1.00  fof(f47,plain,(
% 1.96/1.00    ( ! [X2,X0,X3,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f25])).
% 1.96/1.00  
% 1.96/1.00  fof(f52,plain,(
% 1.96/1.00    v2_pre_topc(sK1)),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f53,plain,(
% 1.96/1.00    l1_pre_topc(sK1)),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f59,plain,(
% 1.96/1.00    ~v2_struct_0(sK4)),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f60,plain,(
% 1.96/1.00    m1_pre_topc(sK4,sK1)),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f3,axiom,(
% 1.96/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f11,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.96/1.00    inference(ennf_transformation,[],[f3])).
% 1.96/1.00  
% 1.96/1.00  fof(f42,plain,(
% 1.96/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f11])).
% 1.96/1.00  
% 1.96/1.00  fof(f2,axiom,(
% 1.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f9,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f2])).
% 1.96/1.00  
% 1.96/1.00  fof(f10,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.96/1.00    inference(flattening,[],[f9])).
% 1.96/1.00  
% 1.96/1.00  fof(f41,plain,(
% 1.96/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f10])).
% 1.96/1.00  
% 1.96/1.00  fof(f68,plain,(
% 1.96/1.00    v3_pre_topc(sK6,sK4)),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f1,axiom,(
% 1.96/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f20,plain,(
% 1.96/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.96/1.00    inference(nnf_transformation,[],[f1])).
% 1.96/1.00  
% 1.96/1.00  fof(f21,plain,(
% 1.96/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.96/1.00    inference(flattening,[],[f20])).
% 1.96/1.00  
% 1.96/1.00  fof(f39,plain,(
% 1.96/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.96/1.00    inference(cnf_transformation,[],[f21])).
% 1.96/1.00  
% 1.96/1.00  fof(f74,plain,(
% 1.96/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.96/1.00    inference(equality_resolution,[],[f39])).
% 1.96/1.00  
% 1.96/1.00  fof(f72,plain,(
% 1.96/1.00    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK2,sK5,sK7)),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f6,axiom,(
% 1.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f16,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f6])).
% 1.96/1.00  
% 1.96/1.00  fof(f17,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f16])).
% 1.96/1.00  
% 1.96/1.00  fof(f26,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(nnf_transformation,[],[f17])).
% 1.96/1.00  
% 1.96/1.00  fof(f50,plain,(
% 1.96/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f26])).
% 1.96/1.00  
% 1.96/1.00  fof(f77,plain,(
% 1.96/1.00    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(equality_resolution,[],[f50])).
% 1.96/1.00  
% 1.96/1.00  fof(f62,plain,(
% 1.96/1.00    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f61,plain,(
% 1.96/1.00    v1_funct_1(sK5)),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f54,plain,(
% 1.96/1.00    ~v2_struct_0(sK2)),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f55,plain,(
% 1.96/1.00    v2_pre_topc(sK2)),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f56,plain,(
% 1.96/1.00    l1_pre_topc(sK2)),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f63,plain,(
% 1.96/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f51,plain,(
% 1.96/1.00    ~v2_struct_0(sK1)),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f57,plain,(
% 1.96/1.00    ~v2_struct_0(sK3)),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f58,plain,(
% 1.96/1.00    m1_pre_topc(sK3,sK1)),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f64,plain,(
% 1.96/1.00    m1_pre_topc(sK3,sK4)),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f67,plain,(
% 1.96/1.00    m1_subset_1(sK8,u1_struct_0(sK3))),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f49,plain,(
% 1.96/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f26])).
% 1.96/1.00  
% 1.96/1.00  fof(f78,plain,(
% 1.96/1.00    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(equality_resolution,[],[f49])).
% 1.96/1.00  
% 1.96/1.00  fof(f5,axiom,(
% 1.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f14,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f5])).
% 1.96/1.00  
% 1.96/1.00  fof(f15,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f14])).
% 1.96/1.00  
% 1.96/1.00  fof(f48,plain,(
% 1.96/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f15])).
% 1.96/1.00  
% 1.96/1.00  fof(f76,plain,(
% 1.96/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(equality_resolution,[],[f48])).
% 1.96/1.00  
% 1.96/1.00  fof(f73,plain,(
% 1.96/1.00    ~r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK2,sK5,sK7)),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f69,plain,(
% 1.96/1.00    r2_hidden(sK7,sK6)),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f70,plain,(
% 1.96/1.00    r1_tarski(sK6,u1_struct_0(sK3))),
% 1.96/1.00    inference(cnf_transformation,[],[f37])).
% 1.96/1.00  
% 1.96/1.00  cnf(c_20,negated_conjecture,
% 1.96/1.00      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 1.96/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2504,plain,
% 1.96/1.00      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_15,negated_conjecture,
% 1.96/1.00      ( sK7 = sK8 ),
% 1.96/1.00      inference(cnf_transformation,[],[f71]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2551,plain,
% 1.96/1.00      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 1.96/1.00      inference(light_normalisation,[status(thm)],[c_2504,c_15]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_21,negated_conjecture,
% 1.96/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.96/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2503,plain,
% 1.96/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_5,plain,
% 1.96/1.00      ( m1_connsp_2(X0,X1,X2)
% 1.96/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.96/1.00      | ~ v3_pre_topc(X3,X1)
% 1.96/1.00      | ~ r2_hidden(X2,X3)
% 1.96/1.00      | ~ r1_tarski(X3,X0)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2515,plain,
% 1.96/1.00      ( m1_connsp_2(X0,X1,X2) = iProver_top
% 1.96/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 1.96/1.00      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 1.96/1.00      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 1.96/1.00      | v3_pre_topc(X3,X1) != iProver_top
% 1.96/1.00      | r2_hidden(X2,X3) != iProver_top
% 1.96/1.00      | r1_tarski(X3,X0) != iProver_top
% 1.96/1.00      | v2_struct_0(X1) = iProver_top
% 1.96/1.00      | l1_pre_topc(X1) != iProver_top
% 1.96/1.00      | v2_pre_topc(X1) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4601,plain,
% 1.96/1.00      ( m1_connsp_2(sK6,sK4,X0) = iProver_top
% 1.96/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.96/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 1.96/1.00      | v3_pre_topc(X1,sK4) != iProver_top
% 1.96/1.00      | r2_hidden(X0,X1) != iProver_top
% 1.96/1.00      | r1_tarski(X1,sK6) != iProver_top
% 1.96/1.00      | v2_struct_0(sK4) = iProver_top
% 1.96/1.00      | l1_pre_topc(sK4) != iProver_top
% 1.96/1.00      | v2_pre_topc(sK4) != iProver_top ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_2503,c_2515]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_34,negated_conjecture,
% 1.96/1.00      ( v2_pre_topc(sK1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_37,plain,
% 1.96/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_33,negated_conjecture,
% 1.96/1.00      ( l1_pre_topc(sK1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_38,plain,
% 1.96/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_27,negated_conjecture,
% 1.96/1.00      ( ~ v2_struct_0(sK4) ),
% 1.96/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_44,plain,
% 1.96/1.00      ( v2_struct_0(sK4) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_26,negated_conjecture,
% 1.96/1.00      ( m1_pre_topc(sK4,sK1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_45,plain,
% 1.96/1.00      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4,plain,
% 1.96/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2849,plain,
% 1.96/1.00      ( ~ m1_pre_topc(X0,sK1) | l1_pre_topc(X0) | ~ l1_pre_topc(sK1) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2850,plain,
% 1.96/1.00      ( m1_pre_topc(X0,sK1) != iProver_top
% 1.96/1.00      | l1_pre_topc(X0) = iProver_top
% 1.96/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_2849]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2852,plain,
% 1.96/1.00      ( m1_pre_topc(sK4,sK1) != iProver_top
% 1.96/1.00      | l1_pre_topc(sK4) = iProver_top
% 1.96/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_2850]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3,plain,
% 1.96/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | v2_pre_topc(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2883,plain,
% 1.96/1.00      ( ~ m1_pre_topc(X0,sK1)
% 1.96/1.00      | ~ l1_pre_topc(sK1)
% 1.96/1.00      | v2_pre_topc(X0)
% 1.96/1.00      | ~ v2_pre_topc(sK1) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2884,plain,
% 1.96/1.00      ( m1_pre_topc(X0,sK1) != iProver_top
% 1.96/1.00      | l1_pre_topc(sK1) != iProver_top
% 1.96/1.00      | v2_pre_topc(X0) = iProver_top
% 1.96/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_2883]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2886,plain,
% 1.96/1.00      ( m1_pre_topc(sK4,sK1) != iProver_top
% 1.96/1.00      | l1_pre_topc(sK1) != iProver_top
% 1.96/1.00      | v2_pre_topc(sK4) = iProver_top
% 1.96/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_2884]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4706,plain,
% 1.96/1.00      ( r1_tarski(X1,sK6) != iProver_top
% 1.96/1.00      | r2_hidden(X0,X1) != iProver_top
% 1.96/1.00      | v3_pre_topc(X1,sK4) != iProver_top
% 1.96/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 1.96/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.96/1.00      | m1_connsp_2(sK6,sK4,X0) = iProver_top ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_4601,c_37,c_38,c_44,c_45,c_2852,c_2886]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4707,plain,
% 1.96/1.00      ( m1_connsp_2(sK6,sK4,X0) = iProver_top
% 1.96/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.96/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 1.96/1.00      | v3_pre_topc(X1,sK4) != iProver_top
% 1.96/1.00      | r2_hidden(X0,X1) != iProver_top
% 1.96/1.00      | r1_tarski(X1,sK6) != iProver_top ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_4706]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4719,plain,
% 1.96/1.00      ( m1_connsp_2(sK6,sK4,X0) = iProver_top
% 1.96/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 1.96/1.00      | v3_pre_topc(sK6,sK4) != iProver_top
% 1.96/1.00      | r2_hidden(X0,sK6) != iProver_top
% 1.96/1.00      | r1_tarski(sK6,sK6) != iProver_top ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_2503,c_4707]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_18,negated_conjecture,
% 1.96/1.00      ( v3_pre_topc(sK6,sK4) ),
% 1.96/1.00      inference(cnf_transformation,[],[f68]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_53,plain,
% 1.96/1.00      ( v3_pre_topc(sK6,sK4) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1,plain,
% 1.96/1.00      ( r1_tarski(X0,X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3702,plain,
% 1.96/1.00      ( r1_tarski(sK6,sK6) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3705,plain,
% 1.96/1.00      ( r1_tarski(sK6,sK6) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_3702]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4759,plain,
% 1.96/1.00      ( r2_hidden(X0,sK6) != iProver_top
% 1.96/1.00      | m1_connsp_2(sK6,sK4,X0) = iProver_top
% 1.96/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_4719,c_53,c_3705]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4760,plain,
% 1.96/1.00      ( m1_connsp_2(sK6,sK4,X0) = iProver_top
% 1.96/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 1.96/1.00      | r2_hidden(X0,sK6) != iProver_top ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_4759]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4768,plain,
% 1.96/1.00      ( m1_connsp_2(sK6,sK4,sK8) = iProver_top
% 1.96/1.00      | r2_hidden(sK8,sK6) != iProver_top ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_2551,c_4760]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_14,negated_conjecture,
% 1.96/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK7)
% 1.96/1.00      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
% 1.96/1.00      inference(cnf_transformation,[],[f72]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2509,plain,
% 1.96/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
% 1.96/1.00      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2574,plain,
% 1.96/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK8) = iProver_top
% 1.96/1.00      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) = iProver_top ),
% 1.96/1.00      inference(light_normalisation,[status(thm)],[c_2509,c_15]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_11,plain,
% 1.96/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 1.96/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.96/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.96/1.00      | ~ m1_connsp_2(X6,X0,X3)
% 1.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.96/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_pre_topc(X0,X5)
% 1.96/1.00      | ~ m1_pre_topc(X4,X5)
% 1.96/1.00      | ~ m1_pre_topc(X4,X0)
% 1.96/1.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.96/1.00      | ~ v1_funct_1(X2)
% 1.96/1.00      | v2_struct_0(X5)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X4)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X5)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X5)
% 1.96/1.00      | ~ v2_pre_topc(X1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f77]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_24,negated_conjecture,
% 1.96/1.00      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 1.96/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_667,plain,
% 1.96/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 1.96/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.96/1.00      | ~ m1_connsp_2(X6,X0,X3)
% 1.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.96/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_pre_topc(X4,X0)
% 1.96/1.00      | ~ m1_pre_topc(X4,X5)
% 1.96/1.00      | ~ m1_pre_topc(X0,X5)
% 1.96/1.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.96/1.00      | ~ v1_funct_1(X2)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X5)
% 1.96/1.00      | v2_struct_0(X4)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X5)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X5)
% 1.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 1.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 1.96/1.00      | sK5 != X2 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_668,plain,
% 1.96/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.96/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 1.96/1.00      | ~ m1_connsp_2(X5,X3,X4)
% 1.96/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.96/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.96/1.00      | ~ m1_pre_topc(X0,X3)
% 1.96/1.00      | ~ m1_pre_topc(X0,X2)
% 1.96/1.00      | ~ m1_pre_topc(X3,X2)
% 1.96/1.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 1.96/1.00      | ~ v1_funct_1(sK5)
% 1.96/1.00      | v2_struct_0(X3)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X2)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X2)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X2)
% 1.96/1.00      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_667]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_25,negated_conjecture,
% 1.96/1.00      ( v1_funct_1(sK5) ),
% 1.96/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_672,plain,
% 1.96/1.00      ( ~ r1_tarski(X5,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_pre_topc(X3,X2)
% 1.96/1.00      | ~ m1_pre_topc(X0,X2)
% 1.96/1.00      | ~ m1_pre_topc(X0,X3)
% 1.96/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.96/1.00      | ~ m1_connsp_2(X5,X3,X4)
% 1.96/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 1.96/1.00      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.96/1.00      | v2_struct_0(X3)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X2)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X2)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X2)
% 1.96/1.00      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_668,c_25]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_673,plain,
% 1.96/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.96/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 1.96/1.00      | ~ m1_connsp_2(X5,X3,X4)
% 1.96/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.96/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.96/1.00      | ~ m1_pre_topc(X3,X2)
% 1.96/1.00      | ~ m1_pre_topc(X0,X3)
% 1.96/1.00      | ~ m1_pre_topc(X0,X2)
% 1.96/1.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X2)
% 1.96/1.00      | v2_struct_0(X3)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X2)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X2)
% 1.96/1.00      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_672]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2489,plain,
% 1.96/1.00      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 1.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 1.96/1.00      | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) != iProver_top
% 1.96/1.00      | r1_tmap_1(X0,X1,sK5,X4) = iProver_top
% 1.96/1.00      | m1_connsp_2(X5,X0,X4) != iProver_top
% 1.96/1.00      | m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 1.96/1.00      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 1.96/1.00      | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
% 1.96/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 1.96/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 1.96/1.00      | m1_pre_topc(X2,X3) != iProver_top
% 1.96/1.00      | m1_pre_topc(X0,X3) != iProver_top
% 1.96/1.00      | r1_tarski(X5,u1_struct_0(X2)) != iProver_top
% 1.96/1.00      | v2_struct_0(X1) = iProver_top
% 1.96/1.00      | v2_struct_0(X2) = iProver_top
% 1.96/1.00      | v2_struct_0(X0) = iProver_top
% 1.96/1.00      | v2_struct_0(X3) = iProver_top
% 1.96/1.00      | l1_pre_topc(X1) != iProver_top
% 1.96/1.00      | l1_pre_topc(X3) != iProver_top
% 1.96/1.00      | v2_pre_topc(X1) != iProver_top
% 1.96/1.00      | v2_pre_topc(X3) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_673]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3014,plain,
% 1.96/1.00      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 1.96/1.00      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
% 1.96/1.00      | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
% 1.96/1.00      | m1_connsp_2(X4,sK4,X3) != iProver_top
% 1.96/1.00      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.96/1.00      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 1.96/1.00      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 1.96/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 1.96/1.00      | m1_pre_topc(X1,X2) != iProver_top
% 1.96/1.00      | m1_pre_topc(X1,sK4) != iProver_top
% 1.96/1.00      | m1_pre_topc(sK4,X2) != iProver_top
% 1.96/1.00      | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
% 1.96/1.00      | v2_struct_0(X1) = iProver_top
% 1.96/1.00      | v2_struct_0(X0) = iProver_top
% 1.96/1.00      | v2_struct_0(X2) = iProver_top
% 1.96/1.00      | v2_struct_0(sK4) = iProver_top
% 1.96/1.00      | l1_pre_topc(X0) != iProver_top
% 1.96/1.00      | l1_pre_topc(X2) != iProver_top
% 1.96/1.00      | v2_pre_topc(X0) != iProver_top
% 1.96/1.00      | v2_pre_topc(X2) != iProver_top ),
% 1.96/1.00      inference(equality_resolution,[status(thm)],[c_2489]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3877,plain,
% 1.96/1.00      ( v2_struct_0(X2) = iProver_top
% 1.96/1.00      | v2_struct_0(X0) = iProver_top
% 1.96/1.00      | v2_struct_0(X1) = iProver_top
% 1.96/1.00      | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
% 1.96/1.00      | m1_pre_topc(sK4,X2) != iProver_top
% 1.96/1.00      | m1_pre_topc(X1,sK4) != iProver_top
% 1.96/1.00      | m1_pre_topc(X1,X2) != iProver_top
% 1.96/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 1.96/1.00      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 1.96/1.00      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 1.96/1.00      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.96/1.00      | m1_connsp_2(X4,sK4,X3) != iProver_top
% 1.96/1.00      | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
% 1.96/1.00      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
% 1.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.96/1.00      | l1_pre_topc(X0) != iProver_top
% 1.96/1.00      | l1_pre_topc(X2) != iProver_top
% 1.96/1.00      | v2_pre_topc(X0) != iProver_top
% 1.96/1.00      | v2_pre_topc(X2) != iProver_top ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_3014,c_44]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3878,plain,
% 1.96/1.00      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 1.96/1.00      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
% 1.96/1.00      | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
% 1.96/1.00      | m1_connsp_2(X4,sK4,X3) != iProver_top
% 1.96/1.00      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.96/1.00      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 1.96/1.00      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 1.96/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 1.96/1.00      | m1_pre_topc(X1,X2) != iProver_top
% 1.96/1.00      | m1_pre_topc(X1,sK4) != iProver_top
% 1.96/1.00      | m1_pre_topc(sK4,X2) != iProver_top
% 1.96/1.00      | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
% 1.96/1.00      | v2_struct_0(X1) = iProver_top
% 1.96/1.00      | v2_struct_0(X0) = iProver_top
% 1.96/1.00      | v2_struct_0(X2) = iProver_top
% 1.96/1.00      | l1_pre_topc(X0) != iProver_top
% 1.96/1.00      | l1_pre_topc(X2) != iProver_top
% 1.96/1.00      | v2_pre_topc(X0) != iProver_top
% 1.96/1.00      | v2_pre_topc(X2) != iProver_top ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_3877]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3900,plain,
% 1.96/1.00      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 1.96/1.00      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 1.96/1.00      | m1_connsp_2(X3,sK4,X2) != iProver_top
% 1.96/1.00      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.96/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 1.96/1.00      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 1.96/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 1.96/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 1.96/1.00      | m1_pre_topc(X0,sK4) != iProver_top
% 1.96/1.00      | m1_pre_topc(sK4,X1) != iProver_top
% 1.96/1.00      | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
% 1.96/1.00      | v2_struct_0(X1) = iProver_top
% 1.96/1.00      | v2_struct_0(X0) = iProver_top
% 1.96/1.00      | v2_struct_0(sK2) = iProver_top
% 1.96/1.00      | l1_pre_topc(X1) != iProver_top
% 1.96/1.00      | l1_pre_topc(sK2) != iProver_top
% 1.96/1.00      | v2_pre_topc(X1) != iProver_top
% 1.96/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 1.96/1.00      inference(equality_resolution,[status(thm)],[c_3878]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_32,negated_conjecture,
% 1.96/1.00      ( ~ v2_struct_0(sK2) ),
% 1.96/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_39,plain,
% 1.96/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_31,negated_conjecture,
% 1.96/1.00      ( v2_pre_topc(sK2) ),
% 1.96/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_40,plain,
% 1.96/1.00      ( v2_pre_topc(sK2) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_30,negated_conjecture,
% 1.96/1.00      ( l1_pre_topc(sK2) ),
% 1.96/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_41,plain,
% 1.96/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_23,negated_conjecture,
% 1.96/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 1.96/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_48,plain,
% 1.96/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4374,plain,
% 1.96/1.00      ( v2_pre_topc(X1) != iProver_top
% 1.96/1.00      | v2_struct_0(X0) = iProver_top
% 1.96/1.00      | v2_struct_0(X1) = iProver_top
% 1.96/1.00      | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
% 1.96/1.00      | m1_pre_topc(sK4,X1) != iProver_top
% 1.96/1.00      | m1_pre_topc(X0,sK4) != iProver_top
% 1.96/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 1.96/1.00      | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 1.96/1.00      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 1.96/1.00      | m1_connsp_2(X3,sK4,X2) != iProver_top
% 1.96/1.00      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.96/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 1.96/1.00      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 1.96/1.00      | l1_pre_topc(X1) != iProver_top ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_3900,c_39,c_40,c_41,c_48]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4375,plain,
% 1.96/1.00      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 1.96/1.00      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 1.96/1.00      | m1_connsp_2(X3,sK4,X2) != iProver_top
% 1.96/1.00      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.96/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 1.96/1.00      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 1.96/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 1.96/1.00      | m1_pre_topc(X0,sK4) != iProver_top
% 1.96/1.00      | m1_pre_topc(sK4,X1) != iProver_top
% 1.96/1.00      | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
% 1.96/1.00      | v2_struct_0(X1) = iProver_top
% 1.96/1.00      | v2_struct_0(X0) = iProver_top
% 1.96/1.00      | l1_pre_topc(X1) != iProver_top
% 1.96/1.00      | v2_pre_topc(X1) != iProver_top ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_4374]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4394,plain,
% 1.96/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK8) = iProver_top
% 1.96/1.00      | m1_connsp_2(X0,sK4,sK8) != iProver_top
% 1.96/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.96/1.00      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 1.96/1.00      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 1.96/1.00      | m1_pre_topc(sK4,sK1) != iProver_top
% 1.96/1.00      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.96/1.00      | m1_pre_topc(sK3,sK1) != iProver_top
% 1.96/1.00      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 1.96/1.00      | v2_struct_0(sK1) = iProver_top
% 1.96/1.00      | v2_struct_0(sK3) = iProver_top
% 1.96/1.00      | l1_pre_topc(sK1) != iProver_top
% 1.96/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_2574,c_4375]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_35,negated_conjecture,
% 1.96/1.00      ( ~ v2_struct_0(sK1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_36,plain,
% 1.96/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_29,negated_conjecture,
% 1.96/1.00      ( ~ v2_struct_0(sK3) ),
% 1.96/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_42,plain,
% 1.96/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_28,negated_conjecture,
% 1.96/1.00      ( m1_pre_topc(sK3,sK1) ),
% 1.96/1.01      inference(cnf_transformation,[],[f58]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_43,plain,
% 1.96/1.01      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 1.96/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_22,negated_conjecture,
% 1.96/1.01      ( m1_pre_topc(sK3,sK4) ),
% 1.96/1.01      inference(cnf_transformation,[],[f64]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_49,plain,
% 1.96/1.01      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 1.96/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_19,negated_conjecture,
% 1.96/1.01      ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
% 1.96/1.01      inference(cnf_transformation,[],[f67]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_52,plain,
% 1.96/1.01      ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
% 1.96/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_12,plain,
% 1.96/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.96/1.01      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.96/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.96/1.01      | ~ m1_connsp_2(X6,X0,X3)
% 1.96/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.96/1.01      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.96/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.96/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.01      | ~ m1_pre_topc(X0,X5)
% 1.96/1.01      | ~ m1_pre_topc(X4,X5)
% 1.96/1.01      | ~ m1_pre_topc(X4,X0)
% 1.96/1.01      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.96/1.01      | ~ v1_funct_1(X2)
% 1.96/1.01      | v2_struct_0(X5)
% 1.96/1.01      | v2_struct_0(X1)
% 1.96/1.01      | v2_struct_0(X4)
% 1.96/1.01      | v2_struct_0(X0)
% 1.96/1.01      | ~ l1_pre_topc(X5)
% 1.96/1.01      | ~ l1_pre_topc(X1)
% 1.96/1.01      | ~ v2_pre_topc(X5)
% 1.96/1.01      | ~ v2_pre_topc(X1) ),
% 1.96/1.01      inference(cnf_transformation,[],[f78]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_10,plain,
% 1.96/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.96/1.01      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.96/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.96/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.96/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.96/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.01      | ~ m1_pre_topc(X4,X0)
% 1.96/1.01      | ~ m1_pre_topc(X4,X5)
% 1.96/1.01      | ~ m1_pre_topc(X0,X5)
% 1.96/1.01      | ~ v1_funct_1(X2)
% 1.96/1.01      | v2_struct_0(X5)
% 1.96/1.01      | v2_struct_0(X1)
% 1.96/1.01      | v2_struct_0(X0)
% 1.96/1.01      | v2_struct_0(X4)
% 1.96/1.01      | ~ l1_pre_topc(X5)
% 1.96/1.01      | ~ l1_pre_topc(X1)
% 1.96/1.01      | ~ v2_pre_topc(X5)
% 1.96/1.01      | ~ v2_pre_topc(X1) ),
% 1.96/1.01      inference(cnf_transformation,[],[f76]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_184,plain,
% 1.96/1.01      ( ~ m1_pre_topc(X4,X0)
% 1.96/1.01      | ~ m1_pre_topc(X4,X5)
% 1.96/1.01      | ~ m1_pre_topc(X0,X5)
% 1.96/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.96/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.96/1.01      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.96/1.01      | ~ r1_tmap_1(X0,X1,X2,X3)
% 1.96/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.96/1.01      | ~ v1_funct_1(X2)
% 1.96/1.01      | v2_struct_0(X5)
% 1.96/1.01      | v2_struct_0(X1)
% 1.96/1.01      | v2_struct_0(X4)
% 1.96/1.01      | v2_struct_0(X0)
% 1.96/1.01      | ~ l1_pre_topc(X5)
% 1.96/1.01      | ~ l1_pre_topc(X1)
% 1.96/1.01      | ~ v2_pre_topc(X5)
% 1.96/1.01      | ~ v2_pre_topc(X1) ),
% 1.96/1.01      inference(global_propositional_subsumption,
% 1.96/1.01                [status(thm)],
% 1.96/1.01                [c_12,c_10]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_185,plain,
% 1.96/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.96/1.01      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.96/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.96/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.96/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.96/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.01      | ~ m1_pre_topc(X4,X0)
% 1.96/1.01      | ~ m1_pre_topc(X4,X5)
% 1.96/1.01      | ~ m1_pre_topc(X0,X5)
% 1.96/1.01      | ~ v1_funct_1(X2)
% 1.96/1.01      | v2_struct_0(X0)
% 1.96/1.01      | v2_struct_0(X1)
% 1.96/1.01      | v2_struct_0(X5)
% 1.96/1.01      | v2_struct_0(X4)
% 1.96/1.01      | ~ l1_pre_topc(X1)
% 1.96/1.01      | ~ l1_pre_topc(X5)
% 1.96/1.01      | ~ v2_pre_topc(X1)
% 1.96/1.01      | ~ v2_pre_topc(X5) ),
% 1.96/1.01      inference(renaming,[status(thm)],[c_184]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_601,plain,
% 1.96/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.96/1.01      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.96/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.96/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.96/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.01      | ~ m1_pre_topc(X4,X0)
% 1.96/1.01      | ~ m1_pre_topc(X4,X5)
% 1.96/1.01      | ~ m1_pre_topc(X0,X5)
% 1.96/1.01      | ~ v1_funct_1(X2)
% 1.96/1.01      | v2_struct_0(X0)
% 1.96/1.01      | v2_struct_0(X1)
% 1.96/1.01      | v2_struct_0(X5)
% 1.96/1.01      | v2_struct_0(X4)
% 1.96/1.01      | ~ l1_pre_topc(X1)
% 1.96/1.01      | ~ l1_pre_topc(X5)
% 1.96/1.01      | ~ v2_pre_topc(X1)
% 1.96/1.01      | ~ v2_pre_topc(X5)
% 1.96/1.01      | u1_struct_0(X0) != u1_struct_0(sK4)
% 1.96/1.01      | u1_struct_0(X1) != u1_struct_0(sK2)
% 1.96/1.01      | sK5 != X2 ),
% 1.96/1.01      inference(resolution_lifted,[status(thm)],[c_185,c_24]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_602,plain,
% 1.96/1.01      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.96/1.01      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 1.96/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.96/1.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.96/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.96/1.01      | ~ m1_pre_topc(X0,X3)
% 1.96/1.01      | ~ m1_pre_topc(X0,X2)
% 1.96/1.01      | ~ m1_pre_topc(X3,X2)
% 1.96/1.01      | ~ v1_funct_1(sK5)
% 1.96/1.01      | v2_struct_0(X3)
% 1.96/1.01      | v2_struct_0(X1)
% 1.96/1.01      | v2_struct_0(X2)
% 1.96/1.01      | v2_struct_0(X0)
% 1.96/1.01      | ~ l1_pre_topc(X1)
% 1.96/1.01      | ~ l1_pre_topc(X2)
% 1.96/1.01      | ~ v2_pre_topc(X1)
% 1.96/1.01      | ~ v2_pre_topc(X2)
% 1.96/1.01      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.96/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 1.96/1.01      inference(unflattening,[status(thm)],[c_601]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_606,plain,
% 1.96/1.01      ( ~ m1_pre_topc(X3,X2)
% 1.96/1.01      | ~ m1_pre_topc(X0,X2)
% 1.96/1.01      | ~ m1_pre_topc(X0,X3)
% 1.96/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.96/1.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.96/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.96/1.01      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 1.96/1.01      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.96/1.01      | v2_struct_0(X3)
% 1.96/1.01      | v2_struct_0(X1)
% 1.96/1.01      | v2_struct_0(X2)
% 1.96/1.01      | v2_struct_0(X0)
% 1.96/1.01      | ~ l1_pre_topc(X1)
% 1.96/1.01      | ~ l1_pre_topc(X2)
% 1.96/1.01      | ~ v2_pre_topc(X1)
% 1.96/1.01      | ~ v2_pre_topc(X2)
% 1.96/1.01      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.96/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 1.96/1.01      inference(global_propositional_subsumption,
% 1.96/1.01                [status(thm)],
% 1.96/1.01                [c_602,c_25]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_607,plain,
% 1.96/1.01      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.96/1.01      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 1.96/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.96/1.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.96/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.96/1.01      | ~ m1_pre_topc(X3,X2)
% 1.96/1.01      | ~ m1_pre_topc(X0,X3)
% 1.96/1.01      | ~ m1_pre_topc(X0,X2)
% 1.96/1.01      | v2_struct_0(X0)
% 1.96/1.01      | v2_struct_0(X1)
% 1.96/1.01      | v2_struct_0(X2)
% 1.96/1.01      | v2_struct_0(X3)
% 1.96/1.01      | ~ l1_pre_topc(X1)
% 1.96/1.01      | ~ l1_pre_topc(X2)
% 1.96/1.01      | ~ v2_pre_topc(X1)
% 1.96/1.01      | ~ v2_pre_topc(X2)
% 1.96/1.01      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.96/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 1.96/1.01      inference(renaming,[status(thm)],[c_606]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_2490,plain,
% 1.96/1.01      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 1.96/1.01      | u1_struct_0(X1) != u1_struct_0(sK2)
% 1.96/1.01      | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) = iProver_top
% 1.96/1.01      | r1_tmap_1(X0,X1,sK5,X4) != iProver_top
% 1.96/1.01      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 1.96/1.01      | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
% 1.96/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 1.96/1.01      | m1_pre_topc(X2,X0) != iProver_top
% 1.96/1.01      | m1_pre_topc(X2,X3) != iProver_top
% 1.96/1.01      | m1_pre_topc(X0,X3) != iProver_top
% 1.96/1.01      | v2_struct_0(X1) = iProver_top
% 1.96/1.01      | v2_struct_0(X2) = iProver_top
% 1.96/1.01      | v2_struct_0(X0) = iProver_top
% 1.96/1.01      | v2_struct_0(X3) = iProver_top
% 1.96/1.01      | l1_pre_topc(X1) != iProver_top
% 1.96/1.01      | l1_pre_topc(X3) != iProver_top
% 1.96/1.01      | v2_pre_topc(X1) != iProver_top
% 1.96/1.01      | v2_pre_topc(X3) != iProver_top ),
% 1.96/1.01      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_3358,plain,
% 1.96/1.01      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 1.96/1.01      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 1.96/1.01      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 1.96/1.01      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 1.96/1.01      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 1.96/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 1.96/1.01      | m1_pre_topc(X1,X2) != iProver_top
% 1.96/1.01      | m1_pre_topc(X1,sK4) != iProver_top
% 1.96/1.01      | m1_pre_topc(sK4,X2) != iProver_top
% 1.96/1.01      | v2_struct_0(X1) = iProver_top
% 1.96/1.01      | v2_struct_0(X0) = iProver_top
% 1.96/1.01      | v2_struct_0(X2) = iProver_top
% 1.96/1.01      | v2_struct_0(sK4) = iProver_top
% 1.96/1.01      | l1_pre_topc(X0) != iProver_top
% 1.96/1.01      | l1_pre_topc(X2) != iProver_top
% 1.96/1.01      | v2_pre_topc(X0) != iProver_top
% 1.96/1.01      | v2_pre_topc(X2) != iProver_top ),
% 1.96/1.01      inference(equality_resolution,[status(thm)],[c_2490]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_3838,plain,
% 1.96/1.01      ( v2_struct_0(X2) = iProver_top
% 1.96/1.01      | v2_struct_0(X0) = iProver_top
% 1.96/1.01      | v2_struct_0(X1) = iProver_top
% 1.96/1.01      | m1_pre_topc(sK4,X2) != iProver_top
% 1.96/1.01      | m1_pre_topc(X1,sK4) != iProver_top
% 1.96/1.01      | m1_pre_topc(X1,X2) != iProver_top
% 1.96/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 1.96/1.01      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 1.96/1.01      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 1.96/1.01      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 1.96/1.01      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 1.96/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.96/1.01      | l1_pre_topc(X0) != iProver_top
% 1.96/1.01      | l1_pre_topc(X2) != iProver_top
% 1.96/1.01      | v2_pre_topc(X0) != iProver_top
% 1.96/1.01      | v2_pre_topc(X2) != iProver_top ),
% 1.96/1.01      inference(global_propositional_subsumption,
% 1.96/1.01                [status(thm)],
% 1.96/1.01                [c_3358,c_44]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_3839,plain,
% 1.96/1.01      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 1.96/1.01      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 1.96/1.01      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 1.96/1.01      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 1.96/1.01      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 1.96/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 1.96/1.01      | m1_pre_topc(X1,X2) != iProver_top
% 1.96/1.01      | m1_pre_topc(X1,sK4) != iProver_top
% 1.96/1.01      | m1_pre_topc(sK4,X2) != iProver_top
% 1.96/1.01      | v2_struct_0(X1) = iProver_top
% 1.96/1.01      | v2_struct_0(X0) = iProver_top
% 1.96/1.01      | v2_struct_0(X2) = iProver_top
% 1.96/1.01      | l1_pre_topc(X0) != iProver_top
% 1.96/1.01      | l1_pre_topc(X2) != iProver_top
% 1.96/1.01      | v2_pre_topc(X0) != iProver_top
% 1.96/1.01      | v2_pre_topc(X2) != iProver_top ),
% 1.96/1.01      inference(renaming,[status(thm)],[c_3838]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_3858,plain,
% 1.96/1.01      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
% 1.96/1.01      | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
% 1.96/1.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 1.96/1.01      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 1.96/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 1.96/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 1.96/1.01      | m1_pre_topc(X0,sK4) != iProver_top
% 1.96/1.01      | m1_pre_topc(sK4,X1) != iProver_top
% 1.96/1.01      | v2_struct_0(X1) = iProver_top
% 1.96/1.01      | v2_struct_0(X0) = iProver_top
% 1.96/1.01      | v2_struct_0(sK2) = iProver_top
% 1.96/1.01      | l1_pre_topc(X1) != iProver_top
% 1.96/1.01      | l1_pre_topc(sK2) != iProver_top
% 1.96/1.01      | v2_pre_topc(X1) != iProver_top
% 1.96/1.01      | v2_pre_topc(sK2) != iProver_top ),
% 1.96/1.01      inference(equality_resolution,[status(thm)],[c_3839]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_3905,plain,
% 1.96/1.01      ( v2_pre_topc(X1) != iProver_top
% 1.96/1.01      | v2_struct_0(X0) = iProver_top
% 1.96/1.01      | v2_struct_0(X1) = iProver_top
% 1.96/1.01      | m1_pre_topc(sK4,X1) != iProver_top
% 1.96/1.01      | m1_pre_topc(X0,sK4) != iProver_top
% 1.96/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 1.96/1.01      | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
% 1.96/1.01      | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
% 1.96/1.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 1.96/1.01      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 1.96/1.01      | l1_pre_topc(X1) != iProver_top ),
% 1.96/1.01      inference(global_propositional_subsumption,
% 1.96/1.01                [status(thm)],
% 1.96/1.01                [c_3858,c_39,c_40,c_41,c_48]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_3906,plain,
% 1.96/1.01      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
% 1.96/1.01      | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
% 1.96/1.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 1.96/1.01      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 1.96/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 1.96/1.01      | m1_pre_topc(X0,sK4) != iProver_top
% 1.96/1.01      | m1_pre_topc(sK4,X1) != iProver_top
% 1.96/1.01      | v2_struct_0(X1) = iProver_top
% 1.96/1.01      | v2_struct_0(X0) = iProver_top
% 1.96/1.01      | l1_pre_topc(X1) != iProver_top
% 1.96/1.01      | v2_pre_topc(X1) != iProver_top ),
% 1.96/1.01      inference(renaming,[status(thm)],[c_3905]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_13,negated_conjecture,
% 1.96/1.01      ( ~ r1_tmap_1(sK4,sK2,sK5,sK7)
% 1.96/1.01      | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
% 1.96/1.01      inference(cnf_transformation,[],[f73]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_2510,plain,
% 1.96/1.01      ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
% 1.96/1.01      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top ),
% 1.96/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_2579,plain,
% 1.96/1.01      ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
% 1.96/1.01      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top ),
% 1.96/1.01      inference(light_normalisation,[status(thm)],[c_2510,c_15]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_3922,plain,
% 1.96/1.01      ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
% 1.96/1.01      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 1.96/1.01      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 1.96/1.01      | m1_pre_topc(sK4,sK1) != iProver_top
% 1.96/1.01      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.96/1.01      | m1_pre_topc(sK3,sK1) != iProver_top
% 1.96/1.01      | v2_struct_0(sK1) = iProver_top
% 1.96/1.01      | v2_struct_0(sK3) = iProver_top
% 1.96/1.01      | l1_pre_topc(sK1) != iProver_top
% 1.96/1.01      | v2_pre_topc(sK1) != iProver_top ),
% 1.96/1.01      inference(superposition,[status(thm)],[c_3906,c_2579]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_4426,plain,
% 1.96/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.96/1.01      | m1_connsp_2(X0,sK4,sK8) != iProver_top
% 1.96/1.01      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
% 1.96/1.01      inference(global_propositional_subsumption,
% 1.96/1.01                [status(thm)],
% 1.96/1.01                [c_4394,c_36,c_37,c_38,c_42,c_43,c_45,c_49,c_52,c_2551,
% 1.96/1.01                 c_3922]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_4427,plain,
% 1.96/1.01      ( m1_connsp_2(X0,sK4,sK8) != iProver_top
% 1.96/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.96/1.01      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
% 1.96/1.01      inference(renaming,[status(thm)],[c_4426]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_4436,plain,
% 1.96/1.01      ( m1_connsp_2(sK6,sK4,sK8) != iProver_top
% 1.96/1.01      | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top ),
% 1.96/1.01      inference(superposition,[status(thm)],[c_2503,c_4427]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_17,negated_conjecture,
% 1.96/1.01      ( r2_hidden(sK7,sK6) ),
% 1.96/1.01      inference(cnf_transformation,[],[f69]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_2507,plain,
% 1.96/1.01      ( r2_hidden(sK7,sK6) = iProver_top ),
% 1.96/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_2546,plain,
% 1.96/1.01      ( r2_hidden(sK8,sK6) = iProver_top ),
% 1.96/1.01      inference(light_normalisation,[status(thm)],[c_2507,c_15]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_16,negated_conjecture,
% 1.96/1.01      ( r1_tarski(sK6,u1_struct_0(sK3)) ),
% 1.96/1.01      inference(cnf_transformation,[],[f70]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_55,plain,
% 1.96/1.01      ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.96/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(contradiction,plain,
% 1.96/1.01      ( $false ),
% 1.96/1.01      inference(minisat,[status(thm)],[c_4768,c_4436,c_2546,c_55]) ).
% 1.96/1.01  
% 1.96/1.01  
% 1.96/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.96/1.01  
% 1.96/1.01  ------                               Statistics
% 1.96/1.01  
% 1.96/1.01  ------ General
% 1.96/1.01  
% 1.96/1.01  abstr_ref_over_cycles:                  0
% 1.96/1.01  abstr_ref_under_cycles:                 0
% 1.96/1.01  gc_basic_clause_elim:                   0
% 1.96/1.01  forced_gc_time:                         0
% 1.96/1.01  parsing_time:                           0.019
% 1.96/1.01  unif_index_cands_time:                  0.
% 1.96/1.01  unif_index_add_time:                    0.
% 1.96/1.01  orderings_time:                         0.
% 1.96/1.01  out_proof_time:                         0.015
% 1.96/1.01  total_time:                             0.187
% 1.96/1.01  num_of_symbols:                         56
% 1.96/1.01  num_of_terms:                           3422
% 1.96/1.01  
% 1.96/1.01  ------ Preprocessing
% 1.96/1.01  
% 1.96/1.01  num_of_splits:                          0
% 1.96/1.01  num_of_split_atoms:                     0
% 1.96/1.01  num_of_reused_defs:                     0
% 1.96/1.01  num_eq_ax_congr_red:                    18
% 1.96/1.01  num_of_sem_filtered_clauses:            1
% 1.96/1.01  num_of_subtypes:                        0
% 1.96/1.01  monotx_restored_types:                  0
% 1.96/1.01  sat_num_of_epr_types:                   0
% 1.96/1.01  sat_num_of_non_cyclic_types:            0
% 1.96/1.01  sat_guarded_non_collapsed_types:        0
% 1.96/1.01  num_pure_diseq_elim:                    0
% 1.96/1.01  simp_replaced_by:                       0
% 1.96/1.01  res_preprocessed:                       162
% 1.96/1.01  prep_upred:                             0
% 1.96/1.01  prep_unflattend:                        25
% 1.96/1.01  smt_new_axioms:                         0
% 1.96/1.01  pred_elim_cands:                        10
% 1.96/1.01  pred_elim:                              2
% 1.96/1.01  pred_elim_cl:                           3
% 1.96/1.01  pred_elim_cycles:                       8
% 1.96/1.01  merged_defs:                            8
% 1.96/1.01  merged_defs_ncl:                        0
% 1.96/1.01  bin_hyper_res:                          8
% 1.96/1.01  prep_cycles:                            4
% 1.96/1.01  pred_elim_time:                         0.027
% 1.96/1.01  splitting_time:                         0.
% 1.96/1.01  sem_filter_time:                        0.
% 1.96/1.01  monotx_time:                            0.001
% 1.96/1.01  subtype_inf_time:                       0.
% 1.96/1.01  
% 1.96/1.01  ------ Problem properties
% 1.96/1.01  
% 1.96/1.01  clauses:                                32
% 1.96/1.01  conjectures:                            21
% 1.96/1.01  epr:                                    18
% 1.96/1.01  horn:                                   24
% 1.96/1.01  ground:                                 21
% 1.96/1.01  unary:                                  20
% 1.96/1.01  binary:                                 2
% 1.96/1.01  lits:                                   111
% 1.96/1.01  lits_eq:                                6
% 1.96/1.01  fd_pure:                                0
% 1.96/1.01  fd_pseudo:                              0
% 1.96/1.01  fd_cond:                                0
% 1.96/1.01  fd_pseudo_cond:                         1
% 1.96/1.01  ac_symbols:                             0
% 1.96/1.01  
% 1.96/1.01  ------ Propositional Solver
% 1.96/1.01  
% 1.96/1.01  prop_solver_calls:                      26
% 1.96/1.01  prop_fast_solver_calls:                 1897
% 1.96/1.01  smt_solver_calls:                       0
% 1.96/1.01  smt_fast_solver_calls:                  0
% 1.96/1.01  prop_num_of_clauses:                    1117
% 1.96/1.01  prop_preprocess_simplified:             4884
% 1.96/1.01  prop_fo_subsumed:                       61
% 1.96/1.01  prop_solver_time:                       0.
% 1.96/1.01  smt_solver_time:                        0.
% 1.96/1.01  smt_fast_solver_time:                   0.
% 1.96/1.01  prop_fast_solver_time:                  0.
% 1.96/1.01  prop_unsat_core_time:                   0.
% 1.96/1.01  
% 1.96/1.01  ------ QBF
% 1.96/1.01  
% 1.96/1.01  qbf_q_res:                              0
% 1.96/1.01  qbf_num_tautologies:                    0
% 1.96/1.01  qbf_prep_cycles:                        0
% 1.96/1.01  
% 1.96/1.01  ------ BMC1
% 1.96/1.01  
% 1.96/1.01  bmc1_current_bound:                     -1
% 1.96/1.01  bmc1_last_solved_bound:                 -1
% 1.96/1.01  bmc1_unsat_core_size:                   -1
% 1.96/1.01  bmc1_unsat_core_parents_size:           -1
% 1.96/1.01  bmc1_merge_next_fun:                    0
% 1.96/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.96/1.01  
% 1.96/1.01  ------ Instantiation
% 1.96/1.01  
% 1.96/1.01  inst_num_of_clauses:                    328
% 1.96/1.01  inst_num_in_passive:                    84
% 1.96/1.01  inst_num_in_active:                     220
% 1.96/1.01  inst_num_in_unprocessed:                24
% 1.96/1.01  inst_num_of_loops:                      240
% 1.96/1.01  inst_num_of_learning_restarts:          0
% 1.96/1.01  inst_num_moves_active_passive:          17
% 1.96/1.01  inst_lit_activity:                      0
% 1.96/1.01  inst_lit_activity_moves:                0
% 1.96/1.01  inst_num_tautologies:                   0
% 1.96/1.01  inst_num_prop_implied:                  0
% 1.96/1.01  inst_num_existing_simplified:           0
% 1.96/1.01  inst_num_eq_res_simplified:             0
% 1.96/1.01  inst_num_child_elim:                    0
% 1.96/1.01  inst_num_of_dismatching_blockings:      18
% 1.96/1.01  inst_num_of_non_proper_insts:           318
% 1.96/1.01  inst_num_of_duplicates:                 0
% 1.96/1.01  inst_inst_num_from_inst_to_res:         0
% 1.96/1.01  inst_dismatching_checking_time:         0.
% 1.96/1.01  
% 1.96/1.01  ------ Resolution
% 1.96/1.01  
% 1.96/1.01  res_num_of_clauses:                     0
% 1.96/1.01  res_num_in_passive:                     0
% 1.96/1.01  res_num_in_active:                      0
% 1.96/1.01  res_num_of_loops:                       166
% 1.96/1.01  res_forward_subset_subsumed:            28
% 1.96/1.01  res_backward_subset_subsumed:           0
% 1.96/1.01  res_forward_subsumed:                   0
% 1.96/1.01  res_backward_subsumed:                  0
% 1.96/1.01  res_forward_subsumption_resolution:     2
% 1.96/1.01  res_backward_subsumption_resolution:    0
% 1.96/1.01  res_clause_to_clause_subsumption:       245
% 1.96/1.01  res_orphan_elimination:                 0
% 1.96/1.01  res_tautology_del:                      32
% 1.96/1.01  res_num_eq_res_simplified:              0
% 1.96/1.01  res_num_sel_changes:                    0
% 1.96/1.01  res_moves_from_active_to_pass:          0
% 1.96/1.01  
% 1.96/1.01  ------ Superposition
% 1.96/1.01  
% 1.96/1.01  sup_time_total:                         0.
% 1.96/1.01  sup_time_generating:                    0.
% 1.96/1.01  sup_time_sim_full:                      0.
% 1.96/1.01  sup_time_sim_immed:                     0.
% 1.96/1.01  
% 1.96/1.01  sup_num_of_clauses:                     50
% 1.96/1.01  sup_num_in_active:                      47
% 1.96/1.01  sup_num_in_passive:                     3
% 1.96/1.01  sup_num_of_loops:                       47
% 1.96/1.01  sup_fw_superposition:                   17
% 1.96/1.01  sup_bw_superposition:                   3
% 1.96/1.01  sup_immediate_simplified:               0
% 1.96/1.01  sup_given_eliminated:                   0
% 1.96/1.01  comparisons_done:                       0
% 1.96/1.01  comparisons_avoided:                    0
% 1.96/1.01  
% 1.96/1.01  ------ Simplifications
% 1.96/1.01  
% 1.96/1.01  
% 1.96/1.01  sim_fw_subset_subsumed:                 0
% 1.96/1.01  sim_bw_subset_subsumed:                 2
% 1.96/1.01  sim_fw_subsumed:                        0
% 1.96/1.01  sim_bw_subsumed:                        0
% 1.96/1.01  sim_fw_subsumption_res:                 0
% 1.96/1.01  sim_bw_subsumption_res:                 0
% 1.96/1.01  sim_tautology_del:                      2
% 1.96/1.01  sim_eq_tautology_del:                   1
% 1.96/1.01  sim_eq_res_simp:                        0
% 1.96/1.01  sim_fw_demodulated:                     0
% 1.96/1.01  sim_bw_demodulated:                     0
% 1.96/1.01  sim_light_normalised:                   4
% 1.96/1.01  sim_joinable_taut:                      0
% 1.96/1.01  sim_joinable_simp:                      0
% 1.96/1.01  sim_ac_normalised:                      0
% 1.96/1.01  sim_smt_subsumption:                    0
% 1.96/1.01  
%------------------------------------------------------------------------------
