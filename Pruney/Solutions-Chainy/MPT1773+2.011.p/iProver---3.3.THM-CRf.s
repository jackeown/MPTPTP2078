%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:10 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  218 (1328 expanded)
%              Number of clauses        :  140 ( 283 expanded)
%              Number of leaves         :   20 ( 553 expanded)
%              Depth                    :   34
%              Number of atoms          : 1750 (27153 expanded)
%              Number of equality atoms :  467 (1928 expanded)
%              Maximal formula depth    :   31 (   8 average)
%              Maximal clause size      :   50 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f34,f42,f41,f40,f39,f38,f37,f36,f35])).

fof(f78,plain,(
    r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f61,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    v3_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
    | r1_tmap_1(sK4,sK2,sK5,sK7) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
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
    inference(equality_resolution,[],[f58])).

fof(f70,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f59,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,(
    m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f43])).

fof(f74,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
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
    inference(equality_resolution,[],[f57])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

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

fof(f56,plain,(
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

fof(f82,plain,(
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
    inference(equality_resolution,[],[f56])).

fof(f81,plain,
    ( ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
    | ~ r1_tmap_1(sK4,sK2,sK5,sK7) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2520,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_3345,plain,
    ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2520])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2515,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_3350,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2515])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2526,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53)))
    | ~ l1_pre_topc(X1_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3340,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53))) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2526])).

cnf(c_4,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2531,plain,
    ( m1_connsp_2(X0_54,X0_53,X1_54)
    | ~ v3_pre_topc(X2_54,X0_53)
    | ~ r2_hidden(X1_54,X2_54)
    | ~ r1_tarski(X2_54,X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ m1_subset_1(X2_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3335,plain,
    ( m1_connsp_2(X0_54,X0_53,X1_54) = iProver_top
    | v3_pre_topc(X2_54,X0_53) != iProver_top
    | r2_hidden(X1_54,X2_54) != iProver_top
    | r1_tarski(X2_54,X0_54) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2531])).

cnf(c_5216,plain,
    ( m1_connsp_2(u1_struct_0(X0_53),X1_53,X0_54) = iProver_top
    | v3_pre_topc(X1_54,X1_53) != iProver_top
    | r2_hidden(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | r1_tarski(X1_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X1_53))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_3340,c_3335])).

cnf(c_6447,plain,
    ( m1_connsp_2(u1_struct_0(X0_53),sK4,X0_54) = iProver_top
    | v3_pre_topc(sK6,sK4) != iProver_top
    | r2_hidden(X0_54,sK6) != iProver_top
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | r1_tarski(sK6,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3350,c_5216])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_39,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_40,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_46,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_47,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_20,negated_conjecture,
    ( v3_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_55,plain,
    ( v3_pre_topc(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2532,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3723,plain,
    ( ~ m1_pre_topc(X0_53,sK1)
    | l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2532])).

cnf(c_3724,plain,
    ( m1_pre_topc(X0_53,sK1) != iProver_top
    | l1_pre_topc(X0_53) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3723])).

cnf(c_3726,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3724])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2533,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v2_pre_topc(X1_53)
    | v2_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3756,plain,
    ( ~ m1_pre_topc(X0_53,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2533])).

cnf(c_3757,plain,
    ( m1_pre_topc(X0_53,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_53) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3756])).

cnf(c_3759,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3757])).

cnf(c_6666,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK6,u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | r2_hidden(X0_54,sK6) != iProver_top
    | m1_connsp_2(u1_struct_0(X0_53),sK4,X0_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6447,c_39,c_40,c_46,c_47,c_55,c_3726,c_3759])).

cnf(c_6667,plain,
    ( m1_connsp_2(u1_struct_0(X0_53),sK4,X0_54) = iProver_top
    | r2_hidden(X0_54,sK6) != iProver_top
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | r1_tarski(sK6,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6666])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2534,plain,
    ( r1_tarski(X0_54,X1_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3332,plain,
    ( r1_tarski(X0_54,X1_54) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2534])).

cnf(c_4376,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | r1_tarski(u1_struct_0(X0_53),u1_struct_0(X1_53)) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_3340,c_3332])).

cnf(c_16,negated_conjecture,
    ( r1_tmap_1(sK4,sK2,sK5,sK7)
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2522,negated_conjecture,
    ( r1_tmap_1(sK4,sK2,sK5,sK7)
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3344,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2522])).

cnf(c_17,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2521,negated_conjecture,
    ( sK7 = sK8 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_3423,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8) = iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3344,c_2521])).

cnf(c_13,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_707,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
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
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_708,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_712,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
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
    inference(global_propositional_subsumption,[status(thm)],[c_708,c_27])).

cnf(c_713,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(renaming,[status(thm)],[c_712])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_760,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(forward_subsumption_resolution,[status(thm)],[c_713,c_11])).

cnf(c_2501,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK5),X0_54)
    | r1_tmap_1(X3_53,X1_53,sK5,X0_54)
    | ~ m1_connsp_2(X1_54,X3_53,X0_54)
    | ~ m1_pre_topc(X3_53,X2_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ r1_tarski(X1_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(X3_53))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X3_53)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X3_53) != u1_struct_0(sK4)
    | u1_struct_0(X1_53) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_760])).

cnf(c_3364,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK4)
    | u1_struct_0(X1_53) != u1_struct_0(sK2)
    | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK5),X0_54) != iProver_top
    | r1_tmap_1(X0_53,X1_53,sK5,X0_54) = iProver_top
    | m1_connsp_2(X1_54,X0_53,X0_54) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | r1_tarski(X1_54,u1_struct_0(X2_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X2_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2501])).

cnf(c_4574,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK4)
    | r1_tmap_1(X1_53,sK2,k3_tmap_1(X2_53,sK2,X0_53,X1_53,sK5),X0_54) != iProver_top
    | r1_tmap_1(X0_53,sK2,sK5,X0_54) = iProver_top
    | m1_connsp_2(X1_54,X0_53,X0_54) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | r1_tarski(X1_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3364])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_41,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_42,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_43,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3697,plain,
    ( ~ r1_tmap_1(X0_53,sK2,k3_tmap_1(X1_53,sK2,X2_53,X0_53,sK5),X0_54)
    | r1_tmap_1(X2_53,sK2,sK5,X0_54)
    | ~ m1_connsp_2(X1_54,X2_53,X0_54)
    | ~ m1_pre_topc(X2_53,X1_53)
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ r1_tarski(X1_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(X2_53))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X2_53)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(sK2))))
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(X2_53) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2501])).

cnf(c_3698,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | r1_tmap_1(X1_53,sK2,k3_tmap_1(X2_53,sK2,X0_53,X1_53,sK5),X0_54) != iProver_top
    | r1_tmap_1(X0_53,sK2,sK5,X0_54) = iProver_top
    | m1_connsp_2(X1_54,X0_53,X0_54) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | r1_tarski(X1_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3697])).

cnf(c_2537,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_3991,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2537])).

cnf(c_5100,plain,
    ( v2_pre_topc(X2_53) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | r1_tarski(X1_54,u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_connsp_2(X1_54,X0_53,X0_54) != iProver_top
    | r1_tmap_1(X0_53,sK2,sK5,X0_54) = iProver_top
    | r1_tmap_1(X1_53,sK2,k3_tmap_1(X2_53,sK2,X0_53,X1_53,sK5),X0_54) != iProver_top
    | u1_struct_0(X0_53) != u1_struct_0(sK4)
    | l1_pre_topc(X2_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4574,c_41,c_42,c_43,c_3698,c_3991])).

cnf(c_5101,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK4)
    | r1_tmap_1(X1_53,sK2,k3_tmap_1(X2_53,sK2,X0_53,X1_53,sK5),X0_54) != iProver_top
    | r1_tmap_1(X0_53,sK2,sK5,X0_54) = iProver_top
    | m1_connsp_2(X1_54,X0_53,X0_54) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | r1_tarski(X1_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5100])).

cnf(c_5122,plain,
    ( r1_tmap_1(X0_53,sK2,k3_tmap_1(X1_53,sK2,sK4,X0_53,sK5),X0_54) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X0_54) = iProver_top
    | m1_connsp_2(X1_54,sK4,X0_54) != iProver_top
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_53) != iProver_top
    | r1_tarski(X1_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5101])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_50,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6321,plain,
    ( v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | r1_tmap_1(X0_53,sK2,k3_tmap_1(X1_53,sK2,sK4,X0_53,sK5),X0_54) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X0_54) = iProver_top
    | m1_connsp_2(X1_54,sK4,X0_54) != iProver_top
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_53) != iProver_top
    | r1_tarski(X1_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5122,c_46,c_50])).

cnf(c_6322,plain,
    ( r1_tmap_1(X0_53,sK2,k3_tmap_1(X1_53,sK2,sK4,X0_53,sK5),X0_54) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X0_54) = iProver_top
    | m1_connsp_2(X1_54,sK4,X0_54) != iProver_top
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_53) != iProver_top
    | r1_tarski(X1_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_6321])).

cnf(c_6340,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8) = iProver_top
    | m1_connsp_2(X0_54,sK4,sK8) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3423,c_6322])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_38,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_44,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_51,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_54,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2516,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_3349,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2516])).

cnf(c_3398,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3349,c_2521])).

cnf(c_14,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_12,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_196,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_12])).

cnf(c_197,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(renaming,[status(thm)],[c_196])).

cnf(c_641,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
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
    inference(resolution_lifted,[status(thm)],[c_197,c_26])).

cnf(c_642,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_646,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
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
    inference(global_propositional_subsumption,[status(thm)],[c_642,c_27])).

cnf(c_647,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(renaming,[status(thm)],[c_646])).

cnf(c_688,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(forward_subsumption_resolution,[status(thm)],[c_647,c_11])).

cnf(c_2502,plain,
    ( r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK5),X0_54)
    | ~ r1_tmap_1(X3_53,X1_53,sK5,X0_54)
    | ~ m1_pre_topc(X3_53,X2_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(X3_53))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X3_53) != u1_struct_0(sK4)
    | u1_struct_0(X1_53) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_688])).

cnf(c_3363,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK4)
    | u1_struct_0(X1_53) != u1_struct_0(sK2)
    | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK5),X0_54) = iProver_top
    | r1_tmap_1(X0_53,X1_53,sK5,X0_54) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X2_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2502])).

cnf(c_4549,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK4)
    | r1_tmap_1(X1_53,sK2,k3_tmap_1(X2_53,sK2,X0_53,X1_53,sK5),X0_54) = iProver_top
    | r1_tmap_1(X0_53,sK2,sK5,X0_54) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3363])).

cnf(c_3687,plain,
    ( r1_tmap_1(X0_53,sK2,k3_tmap_1(X1_53,sK2,X2_53,X0_53,sK5),X0_54)
    | ~ r1_tmap_1(X2_53,sK2,sK5,X0_54)
    | ~ m1_pre_topc(X2_53,X1_53)
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(X2_53))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(sK2))))
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(X2_53) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2502])).

cnf(c_3688,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | r1_tmap_1(X1_53,sK2,k3_tmap_1(X2_53,sK2,X0_53,X1_53,sK5),X0_54) = iProver_top
    | r1_tmap_1(X0_53,sK2,sK5,X0_54) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3687])).

cnf(c_5076,plain,
    ( v2_pre_topc(X2_53) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | r1_tmap_1(X0_53,sK2,sK5,X0_54) != iProver_top
    | r1_tmap_1(X1_53,sK2,k3_tmap_1(X2_53,sK2,X0_53,X1_53,sK5),X0_54) = iProver_top
    | u1_struct_0(X0_53) != u1_struct_0(sK4)
    | l1_pre_topc(X2_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4549,c_41,c_42,c_43])).

cnf(c_5077,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK4)
    | r1_tmap_1(X1_53,sK2,k3_tmap_1(X2_53,sK2,X0_53,X1_53,sK5),X0_54) = iProver_top
    | r1_tmap_1(X0_53,sK2,sK5,X0_54) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5076])).

cnf(c_5095,plain,
    ( r1_tmap_1(X0_53,sK2,k3_tmap_1(X1_53,sK2,sK4,X0_53,sK5),X0_54) = iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X0_54) != iProver_top
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_53) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5077])).

cnf(c_5847,plain,
    ( v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | r1_tmap_1(X0_53,sK2,k3_tmap_1(X1_53,sK2,sK4,X0_53,sK5),X0_54) = iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X0_54) != iProver_top
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_53) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5095,c_46,c_50])).

cnf(c_5848,plain,
    ( r1_tmap_1(X0_53,sK2,k3_tmap_1(X1_53,sK2,sK4,X0_53,sK5),X0_54) = iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X0_54) != iProver_top
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_53) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5847])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK7)
    | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2523,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK7)
    | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3343,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2523])).

cnf(c_3434,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3343,c_2521])).

cnf(c_5863,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5848,c_3434])).

cnf(c_6370,plain,
    ( m1_connsp_2(X0_54,sK4,sK8) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6340,c_38,c_39,c_40,c_44,c_47,c_51,c_54,c_3398,c_5863])).

cnf(c_6380,plain,
    ( m1_connsp_2(u1_struct_0(X0_53),sK4,sK8) != iProver_top
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | r1_tarski(u1_struct_0(X0_53),u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3340,c_6370])).

cnf(c_6652,plain,
    ( r1_tarski(u1_struct_0(X0_53),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | m1_connsp_2(u1_struct_0(X0_53),sK4,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6380,c_40,c_47,c_3726])).

cnf(c_6653,plain,
    ( m1_connsp_2(u1_struct_0(X0_53),sK4,sK8) != iProver_top
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | r1_tarski(u1_struct_0(X0_53),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6652])).

cnf(c_6661,plain,
    ( m1_connsp_2(u1_struct_0(X0_53),sK4,sK8) != iProver_top
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4376,c_6653])).

cnf(c_2514,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3351,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2514])).

cnf(c_3334,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2532])).

cnf(c_4248,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3351,c_3334])).

cnf(c_2524,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_pre_topc(X2_53,X0_53)
    | m1_pre_topc(X2_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v2_pre_topc(X1_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3342,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X2_53,X1_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2524])).

cnf(c_4685,plain,
    ( m1_pre_topc(X0_53,sK4) = iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3351,c_3342])).

cnf(c_4922,plain,
    ( m1_pre_topc(X0_53,sK4) = iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4685,c_39,c_40,c_47,c_3726,c_3759])).

cnf(c_6722,plain,
    ( m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_connsp_2(u1_struct_0(X0_53),sK4,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6661,c_40,c_47,c_3726,c_4248,c_4922])).

cnf(c_6723,plain,
    ( m1_connsp_2(u1_struct_0(X0_53),sK4,sK8) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_6722])).

cnf(c_6730,plain,
    ( r2_hidden(sK8,sK6) != iProver_top
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | r1_tarski(sK6,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6667,c_6723])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2519,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3346,plain,
    ( r2_hidden(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2519])).

cnf(c_3375,plain,
    ( r2_hidden(sK8,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3346,c_2521])).

cnf(c_6795,plain,
    ( r1_tarski(sK6,u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6730,c_3398,c_3375,c_4922])).

cnf(c_6796,plain,
    ( m1_pre_topc(X0_53,sK3) != iProver_top
    | r1_tarski(sK6,u1_struct_0(X0_53)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6795])).

cnf(c_6803,plain,
    ( m1_pre_topc(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3345,c_6796])).

cnf(c_10,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2525,plain,
    ( m1_pre_topc(X0_53,X0_53)
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_6187,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2525])).

cnf(c_6190,plain,
    ( m1_pre_topc(sK3,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6187])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6803,c_6190,c_4248,c_3726,c_47,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.59/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.00  
% 2.59/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.59/1.00  
% 2.59/1.00  ------  iProver source info
% 2.59/1.00  
% 2.59/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.59/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.59/1.00  git: non_committed_changes: false
% 2.59/1.00  git: last_make_outside_of_git: false
% 2.59/1.00  
% 2.59/1.00  ------ 
% 2.59/1.00  
% 2.59/1.00  ------ Input Options
% 2.59/1.00  
% 2.59/1.00  --out_options                           all
% 2.59/1.00  --tptp_safe_out                         true
% 2.59/1.00  --problem_path                          ""
% 2.59/1.00  --include_path                          ""
% 2.59/1.00  --clausifier                            res/vclausify_rel
% 2.59/1.00  --clausifier_options                    --mode clausify
% 2.59/1.00  --stdin                                 false
% 2.59/1.00  --stats_out                             all
% 2.59/1.00  
% 2.59/1.00  ------ General Options
% 2.59/1.00  
% 2.59/1.00  --fof                                   false
% 2.59/1.00  --time_out_real                         305.
% 2.59/1.00  --time_out_virtual                      -1.
% 2.59/1.00  --symbol_type_check                     false
% 2.59/1.00  --clausify_out                          false
% 2.59/1.00  --sig_cnt_out                           false
% 2.59/1.00  --trig_cnt_out                          false
% 2.59/1.00  --trig_cnt_out_tolerance                1.
% 2.59/1.00  --trig_cnt_out_sk_spl                   false
% 2.59/1.00  --abstr_cl_out                          false
% 2.59/1.00  
% 2.59/1.00  ------ Global Options
% 2.59/1.00  
% 2.59/1.00  --schedule                              default
% 2.59/1.00  --add_important_lit                     false
% 2.59/1.00  --prop_solver_per_cl                    1000
% 2.59/1.00  --min_unsat_core                        false
% 2.59/1.00  --soft_assumptions                      false
% 2.59/1.00  --soft_lemma_size                       3
% 2.59/1.00  --prop_impl_unit_size                   0
% 2.59/1.00  --prop_impl_unit                        []
% 2.59/1.00  --share_sel_clauses                     true
% 2.59/1.00  --reset_solvers                         false
% 2.59/1.00  --bc_imp_inh                            [conj_cone]
% 2.59/1.00  --conj_cone_tolerance                   3.
% 2.59/1.00  --extra_neg_conj                        none
% 2.59/1.00  --large_theory_mode                     true
% 2.59/1.00  --prolific_symb_bound                   200
% 2.59/1.00  --lt_threshold                          2000
% 2.59/1.00  --clause_weak_htbl                      true
% 2.59/1.00  --gc_record_bc_elim                     false
% 2.59/1.00  
% 2.59/1.00  ------ Preprocessing Options
% 2.59/1.00  
% 2.59/1.00  --preprocessing_flag                    true
% 2.59/1.00  --time_out_prep_mult                    0.1
% 2.59/1.00  --splitting_mode                        input
% 2.59/1.00  --splitting_grd                         true
% 2.59/1.00  --splitting_cvd                         false
% 2.59/1.00  --splitting_cvd_svl                     false
% 2.59/1.00  --splitting_nvd                         32
% 2.59/1.00  --sub_typing                            true
% 2.59/1.00  --prep_gs_sim                           true
% 2.59/1.00  --prep_unflatten                        true
% 2.59/1.00  --prep_res_sim                          true
% 2.59/1.00  --prep_upred                            true
% 2.59/1.00  --prep_sem_filter                       exhaustive
% 2.59/1.00  --prep_sem_filter_out                   false
% 2.59/1.00  --pred_elim                             true
% 2.59/1.00  --res_sim_input                         true
% 2.59/1.00  --eq_ax_congr_red                       true
% 2.59/1.00  --pure_diseq_elim                       true
% 2.59/1.00  --brand_transform                       false
% 2.59/1.00  --non_eq_to_eq                          false
% 2.59/1.00  --prep_def_merge                        true
% 2.59/1.00  --prep_def_merge_prop_impl              false
% 2.59/1.00  --prep_def_merge_mbd                    true
% 2.59/1.00  --prep_def_merge_tr_red                 false
% 2.59/1.00  --prep_def_merge_tr_cl                  false
% 2.59/1.00  --smt_preprocessing                     true
% 2.59/1.00  --smt_ac_axioms                         fast
% 2.59/1.00  --preprocessed_out                      false
% 2.59/1.00  --preprocessed_stats                    false
% 2.59/1.00  
% 2.59/1.00  ------ Abstraction refinement Options
% 2.59/1.00  
% 2.59/1.00  --abstr_ref                             []
% 2.59/1.00  --abstr_ref_prep                        false
% 2.59/1.00  --abstr_ref_until_sat                   false
% 2.59/1.00  --abstr_ref_sig_restrict                funpre
% 2.59/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/1.00  --abstr_ref_under                       []
% 2.59/1.00  
% 2.59/1.00  ------ SAT Options
% 2.59/1.00  
% 2.59/1.00  --sat_mode                              false
% 2.59/1.00  --sat_fm_restart_options                ""
% 2.59/1.00  --sat_gr_def                            false
% 2.59/1.00  --sat_epr_types                         true
% 2.59/1.00  --sat_non_cyclic_types                  false
% 2.59/1.00  --sat_finite_models                     false
% 2.59/1.00  --sat_fm_lemmas                         false
% 2.59/1.00  --sat_fm_prep                           false
% 2.59/1.00  --sat_fm_uc_incr                        true
% 2.59/1.00  --sat_out_model                         small
% 2.59/1.00  --sat_out_clauses                       false
% 2.59/1.00  
% 2.59/1.00  ------ QBF Options
% 2.59/1.00  
% 2.59/1.00  --qbf_mode                              false
% 2.59/1.00  --qbf_elim_univ                         false
% 2.59/1.00  --qbf_dom_inst                          none
% 2.59/1.00  --qbf_dom_pre_inst                      false
% 2.59/1.00  --qbf_sk_in                             false
% 2.59/1.00  --qbf_pred_elim                         true
% 2.59/1.00  --qbf_split                             512
% 2.59/1.00  
% 2.59/1.00  ------ BMC1 Options
% 2.59/1.00  
% 2.59/1.00  --bmc1_incremental                      false
% 2.59/1.00  --bmc1_axioms                           reachable_all
% 2.59/1.00  --bmc1_min_bound                        0
% 2.59/1.00  --bmc1_max_bound                        -1
% 2.59/1.00  --bmc1_max_bound_default                -1
% 2.59/1.00  --bmc1_symbol_reachability              true
% 2.59/1.00  --bmc1_property_lemmas                  false
% 2.59/1.00  --bmc1_k_induction                      false
% 2.59/1.00  --bmc1_non_equiv_states                 false
% 2.59/1.00  --bmc1_deadlock                         false
% 2.59/1.00  --bmc1_ucm                              false
% 2.59/1.00  --bmc1_add_unsat_core                   none
% 2.59/1.00  --bmc1_unsat_core_children              false
% 2.59/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/1.00  --bmc1_out_stat                         full
% 2.59/1.00  --bmc1_ground_init                      false
% 2.59/1.00  --bmc1_pre_inst_next_state              false
% 2.59/1.00  --bmc1_pre_inst_state                   false
% 2.59/1.00  --bmc1_pre_inst_reach_state             false
% 2.59/1.00  --bmc1_out_unsat_core                   false
% 2.59/1.00  --bmc1_aig_witness_out                  false
% 2.59/1.00  --bmc1_verbose                          false
% 2.59/1.00  --bmc1_dump_clauses_tptp                false
% 2.59/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.59/1.00  --bmc1_dump_file                        -
% 2.59/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.59/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.59/1.00  --bmc1_ucm_extend_mode                  1
% 2.59/1.00  --bmc1_ucm_init_mode                    2
% 2.59/1.00  --bmc1_ucm_cone_mode                    none
% 2.59/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.59/1.00  --bmc1_ucm_relax_model                  4
% 2.59/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.59/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/1.00  --bmc1_ucm_layered_model                none
% 2.59/1.00  --bmc1_ucm_max_lemma_size               10
% 2.59/1.00  
% 2.59/1.00  ------ AIG Options
% 2.59/1.00  
% 2.59/1.00  --aig_mode                              false
% 2.59/1.00  
% 2.59/1.00  ------ Instantiation Options
% 2.59/1.00  
% 2.59/1.00  --instantiation_flag                    true
% 2.59/1.00  --inst_sos_flag                         false
% 2.59/1.00  --inst_sos_phase                        true
% 2.59/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/1.00  --inst_lit_sel_side                     num_symb
% 2.59/1.00  --inst_solver_per_active                1400
% 2.59/1.00  --inst_solver_calls_frac                1.
% 2.59/1.00  --inst_passive_queue_type               priority_queues
% 2.59/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/1.00  --inst_passive_queues_freq              [25;2]
% 2.59/1.00  --inst_dismatching                      true
% 2.59/1.00  --inst_eager_unprocessed_to_passive     true
% 2.59/1.00  --inst_prop_sim_given                   true
% 2.59/1.00  --inst_prop_sim_new                     false
% 2.59/1.00  --inst_subs_new                         false
% 2.59/1.00  --inst_eq_res_simp                      false
% 2.59/1.00  --inst_subs_given                       false
% 2.59/1.00  --inst_orphan_elimination               true
% 2.59/1.00  --inst_learning_loop_flag               true
% 2.59/1.00  --inst_learning_start                   3000
% 2.59/1.00  --inst_learning_factor                  2
% 2.59/1.00  --inst_start_prop_sim_after_learn       3
% 2.59/1.00  --inst_sel_renew                        solver
% 2.59/1.00  --inst_lit_activity_flag                true
% 2.59/1.00  --inst_restr_to_given                   false
% 2.59/1.00  --inst_activity_threshold               500
% 2.59/1.00  --inst_out_proof                        true
% 2.59/1.00  
% 2.59/1.00  ------ Resolution Options
% 2.59/1.00  
% 2.59/1.00  --resolution_flag                       true
% 2.59/1.00  --res_lit_sel                           adaptive
% 2.59/1.00  --res_lit_sel_side                      none
% 2.59/1.00  --res_ordering                          kbo
% 2.59/1.00  --res_to_prop_solver                    active
% 2.59/1.00  --res_prop_simpl_new                    false
% 2.59/1.00  --res_prop_simpl_given                  true
% 2.59/1.00  --res_passive_queue_type                priority_queues
% 2.59/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/1.00  --res_passive_queues_freq               [15;5]
% 2.59/1.00  --res_forward_subs                      full
% 2.59/1.00  --res_backward_subs                     full
% 2.59/1.00  --res_forward_subs_resolution           true
% 2.59/1.00  --res_backward_subs_resolution          true
% 2.59/1.00  --res_orphan_elimination                true
% 2.59/1.00  --res_time_limit                        2.
% 2.59/1.00  --res_out_proof                         true
% 2.59/1.00  
% 2.59/1.00  ------ Superposition Options
% 2.59/1.00  
% 2.59/1.00  --superposition_flag                    true
% 2.59/1.00  --sup_passive_queue_type                priority_queues
% 2.59/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.59/1.00  --demod_completeness_check              fast
% 2.59/1.00  --demod_use_ground                      true
% 2.59/1.00  --sup_to_prop_solver                    passive
% 2.59/1.00  --sup_prop_simpl_new                    true
% 2.59/1.00  --sup_prop_simpl_given                  true
% 2.59/1.00  --sup_fun_splitting                     false
% 2.59/1.00  --sup_smt_interval                      50000
% 2.59/1.00  
% 2.59/1.00  ------ Superposition Simplification Setup
% 2.59/1.00  
% 2.59/1.00  --sup_indices_passive                   []
% 2.59/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/1.00  --sup_full_bw                           [BwDemod]
% 2.59/1.00  --sup_immed_triv                        [TrivRules]
% 2.59/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/1.00  --sup_immed_bw_main                     []
% 2.59/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/1.00  
% 2.59/1.00  ------ Combination Options
% 2.59/1.00  
% 2.59/1.00  --comb_res_mult                         3
% 2.59/1.00  --comb_sup_mult                         2
% 2.59/1.00  --comb_inst_mult                        10
% 2.59/1.00  
% 2.59/1.00  ------ Debug Options
% 2.59/1.00  
% 2.59/1.00  --dbg_backtrace                         false
% 2.59/1.00  --dbg_dump_prop_clauses                 false
% 2.59/1.00  --dbg_dump_prop_clauses_file            -
% 2.59/1.00  --dbg_out_stat                          false
% 2.59/1.00  ------ Parsing...
% 2.59/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.59/1.00  
% 2.59/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.59/1.00  
% 2.59/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.59/1.00  
% 2.59/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.59/1.00  ------ Proving...
% 2.59/1.00  ------ Problem Properties 
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  clauses                                 35
% 2.59/1.00  conjectures                             21
% 2.59/1.00  EPR                                     18
% 2.59/1.00  Horn                                    27
% 2.59/1.00  unary                                   19
% 2.59/1.00  binary                                  5
% 2.59/1.00  lits                                    119
% 2.59/1.00  lits eq                                 5
% 2.59/1.00  fd_pure                                 0
% 2.59/1.00  fd_pseudo                               0
% 2.59/1.00  fd_cond                                 0
% 2.59/1.00  fd_pseudo_cond                          0
% 2.59/1.00  AC symbols                              0
% 2.59/1.00  
% 2.59/1.00  ------ Schedule dynamic 5 is on 
% 2.59/1.00  
% 2.59/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  ------ 
% 2.59/1.00  Current options:
% 2.59/1.00  ------ 
% 2.59/1.00  
% 2.59/1.00  ------ Input Options
% 2.59/1.00  
% 2.59/1.00  --out_options                           all
% 2.59/1.00  --tptp_safe_out                         true
% 2.59/1.00  --problem_path                          ""
% 2.59/1.00  --include_path                          ""
% 2.59/1.00  --clausifier                            res/vclausify_rel
% 2.59/1.00  --clausifier_options                    --mode clausify
% 2.59/1.00  --stdin                                 false
% 2.59/1.00  --stats_out                             all
% 2.59/1.00  
% 2.59/1.00  ------ General Options
% 2.59/1.00  
% 2.59/1.00  --fof                                   false
% 2.59/1.00  --time_out_real                         305.
% 2.59/1.00  --time_out_virtual                      -1.
% 2.59/1.00  --symbol_type_check                     false
% 2.59/1.00  --clausify_out                          false
% 2.59/1.00  --sig_cnt_out                           false
% 2.59/1.00  --trig_cnt_out                          false
% 2.59/1.00  --trig_cnt_out_tolerance                1.
% 2.59/1.00  --trig_cnt_out_sk_spl                   false
% 2.59/1.00  --abstr_cl_out                          false
% 2.59/1.00  
% 2.59/1.00  ------ Global Options
% 2.59/1.00  
% 2.59/1.00  --schedule                              default
% 2.59/1.00  --add_important_lit                     false
% 2.59/1.00  --prop_solver_per_cl                    1000
% 2.59/1.00  --min_unsat_core                        false
% 2.59/1.00  --soft_assumptions                      false
% 2.59/1.00  --soft_lemma_size                       3
% 2.59/1.00  --prop_impl_unit_size                   0
% 2.59/1.00  --prop_impl_unit                        []
% 2.59/1.00  --share_sel_clauses                     true
% 2.59/1.00  --reset_solvers                         false
% 2.59/1.00  --bc_imp_inh                            [conj_cone]
% 2.59/1.00  --conj_cone_tolerance                   3.
% 2.59/1.00  --extra_neg_conj                        none
% 2.59/1.00  --large_theory_mode                     true
% 2.59/1.00  --prolific_symb_bound                   200
% 2.59/1.00  --lt_threshold                          2000
% 2.59/1.00  --clause_weak_htbl                      true
% 2.59/1.00  --gc_record_bc_elim                     false
% 2.59/1.00  
% 2.59/1.00  ------ Preprocessing Options
% 2.59/1.00  
% 2.59/1.00  --preprocessing_flag                    true
% 2.59/1.00  --time_out_prep_mult                    0.1
% 2.59/1.00  --splitting_mode                        input
% 2.59/1.00  --splitting_grd                         true
% 2.59/1.00  --splitting_cvd                         false
% 2.59/1.00  --splitting_cvd_svl                     false
% 2.59/1.00  --splitting_nvd                         32
% 2.59/1.00  --sub_typing                            true
% 2.59/1.00  --prep_gs_sim                           true
% 2.59/1.00  --prep_unflatten                        true
% 2.59/1.00  --prep_res_sim                          true
% 2.59/1.00  --prep_upred                            true
% 2.59/1.00  --prep_sem_filter                       exhaustive
% 2.59/1.00  --prep_sem_filter_out                   false
% 2.59/1.00  --pred_elim                             true
% 2.59/1.00  --res_sim_input                         true
% 2.59/1.00  --eq_ax_congr_red                       true
% 2.59/1.00  --pure_diseq_elim                       true
% 2.59/1.00  --brand_transform                       false
% 2.59/1.00  --non_eq_to_eq                          false
% 2.59/1.00  --prep_def_merge                        true
% 2.59/1.00  --prep_def_merge_prop_impl              false
% 2.59/1.00  --prep_def_merge_mbd                    true
% 2.59/1.00  --prep_def_merge_tr_red                 false
% 2.59/1.00  --prep_def_merge_tr_cl                  false
% 2.59/1.00  --smt_preprocessing                     true
% 2.59/1.00  --smt_ac_axioms                         fast
% 2.59/1.00  --preprocessed_out                      false
% 2.59/1.00  --preprocessed_stats                    false
% 2.59/1.00  
% 2.59/1.00  ------ Abstraction refinement Options
% 2.59/1.00  
% 2.59/1.00  --abstr_ref                             []
% 2.59/1.00  --abstr_ref_prep                        false
% 2.59/1.00  --abstr_ref_until_sat                   false
% 2.59/1.00  --abstr_ref_sig_restrict                funpre
% 2.59/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/1.00  --abstr_ref_under                       []
% 2.59/1.00  
% 2.59/1.00  ------ SAT Options
% 2.59/1.00  
% 2.59/1.00  --sat_mode                              false
% 2.59/1.00  --sat_fm_restart_options                ""
% 2.59/1.00  --sat_gr_def                            false
% 2.59/1.00  --sat_epr_types                         true
% 2.59/1.00  --sat_non_cyclic_types                  false
% 2.59/1.00  --sat_finite_models                     false
% 2.59/1.00  --sat_fm_lemmas                         false
% 2.59/1.00  --sat_fm_prep                           false
% 2.59/1.00  --sat_fm_uc_incr                        true
% 2.59/1.00  --sat_out_model                         small
% 2.59/1.00  --sat_out_clauses                       false
% 2.59/1.00  
% 2.59/1.00  ------ QBF Options
% 2.59/1.00  
% 2.59/1.00  --qbf_mode                              false
% 2.59/1.00  --qbf_elim_univ                         false
% 2.59/1.00  --qbf_dom_inst                          none
% 2.59/1.00  --qbf_dom_pre_inst                      false
% 2.59/1.00  --qbf_sk_in                             false
% 2.59/1.00  --qbf_pred_elim                         true
% 2.59/1.00  --qbf_split                             512
% 2.59/1.00  
% 2.59/1.00  ------ BMC1 Options
% 2.59/1.00  
% 2.59/1.00  --bmc1_incremental                      false
% 2.59/1.00  --bmc1_axioms                           reachable_all
% 2.59/1.00  --bmc1_min_bound                        0
% 2.59/1.00  --bmc1_max_bound                        -1
% 2.59/1.00  --bmc1_max_bound_default                -1
% 2.59/1.00  --bmc1_symbol_reachability              true
% 2.59/1.00  --bmc1_property_lemmas                  false
% 2.59/1.00  --bmc1_k_induction                      false
% 2.59/1.00  --bmc1_non_equiv_states                 false
% 2.59/1.00  --bmc1_deadlock                         false
% 2.59/1.00  --bmc1_ucm                              false
% 2.59/1.00  --bmc1_add_unsat_core                   none
% 2.59/1.00  --bmc1_unsat_core_children              false
% 2.59/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/1.00  --bmc1_out_stat                         full
% 2.59/1.00  --bmc1_ground_init                      false
% 2.59/1.00  --bmc1_pre_inst_next_state              false
% 2.59/1.00  --bmc1_pre_inst_state                   false
% 2.59/1.00  --bmc1_pre_inst_reach_state             false
% 2.59/1.00  --bmc1_out_unsat_core                   false
% 2.59/1.00  --bmc1_aig_witness_out                  false
% 2.59/1.00  --bmc1_verbose                          false
% 2.59/1.00  --bmc1_dump_clauses_tptp                false
% 2.59/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.59/1.00  --bmc1_dump_file                        -
% 2.59/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.59/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.59/1.00  --bmc1_ucm_extend_mode                  1
% 2.59/1.00  --bmc1_ucm_init_mode                    2
% 2.59/1.00  --bmc1_ucm_cone_mode                    none
% 2.59/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.59/1.00  --bmc1_ucm_relax_model                  4
% 2.59/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.59/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/1.00  --bmc1_ucm_layered_model                none
% 2.59/1.00  --bmc1_ucm_max_lemma_size               10
% 2.59/1.00  
% 2.59/1.00  ------ AIG Options
% 2.59/1.00  
% 2.59/1.00  --aig_mode                              false
% 2.59/1.00  
% 2.59/1.00  ------ Instantiation Options
% 2.59/1.00  
% 2.59/1.00  --instantiation_flag                    true
% 2.59/1.00  --inst_sos_flag                         false
% 2.59/1.00  --inst_sos_phase                        true
% 2.59/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/1.00  --inst_lit_sel_side                     none
% 2.59/1.00  --inst_solver_per_active                1400
% 2.59/1.00  --inst_solver_calls_frac                1.
% 2.59/1.00  --inst_passive_queue_type               priority_queues
% 2.59/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/1.00  --inst_passive_queues_freq              [25;2]
% 2.59/1.00  --inst_dismatching                      true
% 2.59/1.00  --inst_eager_unprocessed_to_passive     true
% 2.59/1.00  --inst_prop_sim_given                   true
% 2.59/1.00  --inst_prop_sim_new                     false
% 2.59/1.00  --inst_subs_new                         false
% 2.59/1.00  --inst_eq_res_simp                      false
% 2.59/1.00  --inst_subs_given                       false
% 2.59/1.00  --inst_orphan_elimination               true
% 2.59/1.00  --inst_learning_loop_flag               true
% 2.59/1.00  --inst_learning_start                   3000
% 2.59/1.00  --inst_learning_factor                  2
% 2.59/1.00  --inst_start_prop_sim_after_learn       3
% 2.59/1.00  --inst_sel_renew                        solver
% 2.59/1.00  --inst_lit_activity_flag                true
% 2.59/1.00  --inst_restr_to_given                   false
% 2.59/1.00  --inst_activity_threshold               500
% 2.59/1.00  --inst_out_proof                        true
% 2.59/1.00  
% 2.59/1.00  ------ Resolution Options
% 2.59/1.00  
% 2.59/1.00  --resolution_flag                       false
% 2.59/1.00  --res_lit_sel                           adaptive
% 2.59/1.00  --res_lit_sel_side                      none
% 2.59/1.00  --res_ordering                          kbo
% 2.59/1.00  --res_to_prop_solver                    active
% 2.59/1.00  --res_prop_simpl_new                    false
% 2.59/1.00  --res_prop_simpl_given                  true
% 2.59/1.00  --res_passive_queue_type                priority_queues
% 2.59/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/1.00  --res_passive_queues_freq               [15;5]
% 2.59/1.00  --res_forward_subs                      full
% 2.59/1.00  --res_backward_subs                     full
% 2.59/1.00  --res_forward_subs_resolution           true
% 2.59/1.00  --res_backward_subs_resolution          true
% 2.59/1.00  --res_orphan_elimination                true
% 2.59/1.00  --res_time_limit                        2.
% 2.59/1.00  --res_out_proof                         true
% 2.59/1.00  
% 2.59/1.00  ------ Superposition Options
% 2.59/1.00  
% 2.59/1.00  --superposition_flag                    true
% 2.59/1.00  --sup_passive_queue_type                priority_queues
% 2.59/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.59/1.00  --demod_completeness_check              fast
% 2.59/1.00  --demod_use_ground                      true
% 2.59/1.00  --sup_to_prop_solver                    passive
% 2.59/1.00  --sup_prop_simpl_new                    true
% 2.59/1.00  --sup_prop_simpl_given                  true
% 2.59/1.00  --sup_fun_splitting                     false
% 2.59/1.00  --sup_smt_interval                      50000
% 2.59/1.00  
% 2.59/1.00  ------ Superposition Simplification Setup
% 2.59/1.00  
% 2.59/1.00  --sup_indices_passive                   []
% 2.59/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/1.00  --sup_full_bw                           [BwDemod]
% 2.59/1.00  --sup_immed_triv                        [TrivRules]
% 2.59/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/1.00  --sup_immed_bw_main                     []
% 2.59/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/1.00  
% 2.59/1.00  ------ Combination Options
% 2.59/1.00  
% 2.59/1.00  --comb_res_mult                         3
% 2.59/1.00  --comb_sup_mult                         2
% 2.59/1.00  --comb_inst_mult                        10
% 2.59/1.00  
% 2.59/1.00  ------ Debug Options
% 2.59/1.00  
% 2.59/1.00  --dbg_backtrace                         false
% 2.59/1.00  --dbg_dump_prop_clauses                 false
% 2.59/1.00  --dbg_dump_prop_clauses_file            -
% 2.59/1.00  --dbg_out_stat                          false
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  ------ Proving...
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  % SZS status Theorem for theBenchmark.p
% 2.59/1.00  
% 2.59/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.59/1.00  
% 2.59/1.00  fof(f10,conjecture,(
% 2.59/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f11,negated_conjecture,(
% 2.59/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.59/1.00    inference(negated_conjecture,[],[f10])).
% 2.59/1.00  
% 2.59/1.00  fof(f25,plain,(
% 2.59/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.59/1.00    inference(ennf_transformation,[],[f11])).
% 2.59/1.00  
% 2.59/1.00  fof(f26,plain,(
% 2.59/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.59/1.00    inference(flattening,[],[f25])).
% 2.59/1.00  
% 2.59/1.00  fof(f33,plain,(
% 2.59/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.59/1.00    inference(nnf_transformation,[],[f26])).
% 2.59/1.00  
% 2.59/1.00  fof(f34,plain,(
% 2.59/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.59/1.00    inference(flattening,[],[f33])).
% 2.59/1.00  
% 2.59/1.00  fof(f42,plain,(
% 2.59/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8) | r1_tmap_1(X3,X1,X4,X6)) & sK8 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(sK8,u1_struct_0(X2)))) )),
% 2.59/1.00    introduced(choice_axiom,[])).
% 2.59/1.00  
% 2.59/1.00  fof(f41,plain,(
% 2.59/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,sK7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,sK7)) & sK7 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK7,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 2.59/1.00    introduced(choice_axiom,[])).
% 2.59/1.00  
% 2.59/1.00  fof(f40,plain,(
% 2.59/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(sK6,u1_struct_0(X2)) & r2_hidden(X6,sK6) & v3_pre_topc(sK6,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X3))))) )),
% 2.59/1.00    introduced(choice_axiom,[])).
% 2.59/1.00  
% 2.59/1.00  fof(f39,plain,(
% 2.59/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X7) | ~r1_tmap_1(X3,X1,sK5,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X7) | r1_tmap_1(X3,X1,sK5,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 2.59/1.00    introduced(choice_axiom,[])).
% 2.59/1.00  
% 2.59/1.00  fof(f38,plain,(
% 2.59/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X7) | ~r1_tmap_1(sK4,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X7) | r1_tmap_1(sK4,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK4) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_pre_topc(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.59/1.00    introduced(choice_axiom,[])).
% 2.59/1.00  
% 2.59/1.00  fof(f37,plain,(
% 2.59/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK3)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(sK3))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.59/1.00    introduced(choice_axiom,[])).
% 2.59/1.00  
% 2.59/1.00  fof(f36,plain,(
% 2.59/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK2,X4,X6)) & (r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X7) | r1_tmap_1(X3,sK2,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.59/1.00    introduced(choice_axiom,[])).
% 2.59/1.00  
% 2.59/1.00  fof(f35,plain,(
% 2.59/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.59/1.00    introduced(choice_axiom,[])).
% 2.59/1.00  
% 2.59/1.00  fof(f43,plain,(
% 2.59/1.00    ((((((((~r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK2,sK5,sK7)) & (r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK2,sK5,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK3)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK4) & m1_subset_1(sK8,u1_struct_0(sK3))) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_pre_topc(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f34,f42,f41,f40,f39,f38,f37,f36,f35])).
% 2.59/1.00  
% 2.59/1.00  fof(f78,plain,(
% 2.59/1.00    r1_tarski(sK6,u1_struct_0(sK3))),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f73,plain,(
% 2.59/1.00    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f5,axiom,(
% 2.59/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f17,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.59/1.00    inference(ennf_transformation,[],[f5])).
% 2.59/1.00  
% 2.59/1.00  fof(f53,plain,(
% 2.59/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f17])).
% 2.59/1.00  
% 2.59/1.00  fof(f4,axiom,(
% 2.59/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 2.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f15,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.59/1.00    inference(ennf_transformation,[],[f4])).
% 2.59/1.00  
% 2.59/1.00  fof(f16,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.59/1.00    inference(flattening,[],[f15])).
% 2.59/1.00  
% 2.59/1.00  fof(f28,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.59/1.00    inference(nnf_transformation,[],[f16])).
% 2.59/1.00  
% 2.59/1.00  fof(f29,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.59/1.00    inference(rectify,[],[f28])).
% 2.59/1.00  
% 2.59/1.00  fof(f30,plain,(
% 2.59/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK0(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.59/1.00    introduced(choice_axiom,[])).
% 2.59/1.00  
% 2.59/1.00  fof(f31,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK0(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 2.59/1.00  
% 2.59/1.00  fof(f52,plain,(
% 2.59/1.00    ( ! [X2,X0,X3,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f31])).
% 2.59/1.00  
% 2.59/1.00  fof(f60,plain,(
% 2.59/1.00    v2_pre_topc(sK1)),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f61,plain,(
% 2.59/1.00    l1_pre_topc(sK1)),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f67,plain,(
% 2.59/1.00    ~v2_struct_0(sK4)),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f68,plain,(
% 2.59/1.00    m1_pre_topc(sK4,sK1)),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f76,plain,(
% 2.59/1.00    v3_pre_topc(sK6,sK4)),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f3,axiom,(
% 2.59/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f14,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.59/1.00    inference(ennf_transformation,[],[f3])).
% 2.59/1.00  
% 2.59/1.00  fof(f47,plain,(
% 2.59/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f14])).
% 2.59/1.00  
% 2.59/1.00  fof(f2,axiom,(
% 2.59/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f12,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.59/1.00    inference(ennf_transformation,[],[f2])).
% 2.59/1.00  
% 2.59/1.00  fof(f13,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.59/1.00    inference(flattening,[],[f12])).
% 2.59/1.00  
% 2.59/1.00  fof(f46,plain,(
% 2.59/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f13])).
% 2.59/1.00  
% 2.59/1.00  fof(f1,axiom,(
% 2.59/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f27,plain,(
% 2.59/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.59/1.00    inference(nnf_transformation,[],[f1])).
% 2.59/1.00  
% 2.59/1.00  fof(f44,plain,(
% 2.59/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.59/1.00    inference(cnf_transformation,[],[f27])).
% 2.59/1.00  
% 2.59/1.00  fof(f80,plain,(
% 2.59/1.00    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK2,sK5,sK7)),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f79,plain,(
% 2.59/1.00    sK7 = sK8),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f9,axiom,(
% 2.59/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f23,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.59/1.00    inference(ennf_transformation,[],[f9])).
% 2.59/1.00  
% 2.59/1.00  fof(f24,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.59/1.00    inference(flattening,[],[f23])).
% 2.59/1.00  
% 2.59/1.00  fof(f32,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.59/1.00    inference(nnf_transformation,[],[f24])).
% 2.59/1.00  
% 2.59/1.00  fof(f58,plain,(
% 2.59/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f32])).
% 2.59/1.00  
% 2.59/1.00  fof(f83,plain,(
% 2.59/1.00    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.59/1.00    inference(equality_resolution,[],[f58])).
% 2.59/1.00  
% 2.59/1.00  fof(f70,plain,(
% 2.59/1.00    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f69,plain,(
% 2.59/1.00    v1_funct_1(sK5)),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f7,axiom,(
% 2.59/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f19,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.59/1.00    inference(ennf_transformation,[],[f7])).
% 2.59/1.00  
% 2.59/1.00  fof(f20,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.59/1.00    inference(flattening,[],[f19])).
% 2.59/1.00  
% 2.59/1.00  fof(f55,plain,(
% 2.59/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f20])).
% 2.59/1.00  
% 2.59/1.00  fof(f62,plain,(
% 2.59/1.00    ~v2_struct_0(sK2)),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f63,plain,(
% 2.59/1.00    v2_pre_topc(sK2)),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f64,plain,(
% 2.59/1.00    l1_pre_topc(sK2)),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f71,plain,(
% 2.59/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f59,plain,(
% 2.59/1.00    ~v2_struct_0(sK1)),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f65,plain,(
% 2.59/1.00    ~v2_struct_0(sK3)),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f72,plain,(
% 2.59/1.00    m1_pre_topc(sK3,sK4)),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f75,plain,(
% 2.59/1.00    m1_subset_1(sK8,u1_struct_0(sK3))),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f74,plain,(
% 2.59/1.00    m1_subset_1(sK7,u1_struct_0(sK4))),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f57,plain,(
% 2.59/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f32])).
% 2.59/1.00  
% 2.59/1.00  fof(f84,plain,(
% 2.59/1.00    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.59/1.00    inference(equality_resolution,[],[f57])).
% 2.59/1.00  
% 2.59/1.00  fof(f8,axiom,(
% 2.59/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 2.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f21,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.59/1.00    inference(ennf_transformation,[],[f8])).
% 2.59/1.00  
% 2.59/1.00  fof(f22,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.59/1.00    inference(flattening,[],[f21])).
% 2.59/1.00  
% 2.59/1.00  fof(f56,plain,(
% 2.59/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f22])).
% 2.59/1.00  
% 2.59/1.00  fof(f82,plain,(
% 2.59/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.59/1.00    inference(equality_resolution,[],[f56])).
% 2.59/1.00  
% 2.59/1.00  fof(f81,plain,(
% 2.59/1.00    ~r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK2,sK5,sK7)),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f77,plain,(
% 2.59/1.00    r2_hidden(sK7,sK6)),
% 2.59/1.00    inference(cnf_transformation,[],[f43])).
% 2.59/1.00  
% 2.59/1.00  fof(f6,axiom,(
% 2.59/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f18,plain,(
% 2.59/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.59/1.00    inference(ennf_transformation,[],[f6])).
% 2.59/1.00  
% 2.59/1.00  fof(f54,plain,(
% 2.59/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f18])).
% 2.59/1.00  
% 2.59/1.00  cnf(c_18,negated_conjecture,
% 2.59/1.00      ( r1_tarski(sK6,u1_struct_0(sK3)) ),
% 2.59/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2520,negated_conjecture,
% 2.59/1.00      ( r1_tarski(sK6,u1_struct_0(sK3)) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3345,plain,
% 2.59/1.00      ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2520]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_23,negated_conjecture,
% 2.59/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.59/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2515,negated_conjecture,
% 2.59/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3350,plain,
% 2.59/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2515]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_9,plain,
% 2.59/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.59/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | ~ l1_pre_topc(X1) ),
% 2.59/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2526,plain,
% 2.59/1.00      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.59/1.00      | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53)))
% 2.59/1.00      | ~ l1_pre_topc(X1_53) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3340,plain,
% 2.59/1.00      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.59/1.00      | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53))) = iProver_top
% 2.59/1.00      | l1_pre_topc(X1_53) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2526]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_4,plain,
% 2.59/1.00      ( m1_connsp_2(X0,X1,X2)
% 2.59/1.00      | ~ v3_pre_topc(X3,X1)
% 2.59/1.00      | ~ r2_hidden(X2,X3)
% 2.59/1.00      | ~ r1_tarski(X3,X0)
% 2.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.59/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | v2_struct_0(X1)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X1) ),
% 2.59/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2531,plain,
% 2.59/1.00      ( m1_connsp_2(X0_54,X0_53,X1_54)
% 2.59/1.00      | ~ v3_pre_topc(X2_54,X0_53)
% 2.59/1.00      | ~ r2_hidden(X1_54,X2_54)
% 2.59/1.00      | ~ r1_tarski(X2_54,X0_54)
% 2.59/1.00      | ~ m1_subset_1(X1_54,u1_struct_0(X0_53))
% 2.59/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.59/1.00      | ~ m1_subset_1(X2_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.59/1.00      | v2_struct_0(X0_53)
% 2.59/1.00      | ~ l1_pre_topc(X0_53)
% 2.59/1.00      | ~ v2_pre_topc(X0_53) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3335,plain,
% 2.59/1.00      ( m1_connsp_2(X0_54,X0_53,X1_54) = iProver_top
% 2.59/1.00      | v3_pre_topc(X2_54,X0_53) != iProver_top
% 2.59/1.00      | r2_hidden(X1_54,X2_54) != iProver_top
% 2.59/1.00      | r1_tarski(X2_54,X0_54) != iProver_top
% 2.59/1.00      | m1_subset_1(X1_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.59/1.00      | m1_subset_1(X2_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.59/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.59/1.00      | l1_pre_topc(X0_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(X0_53) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2531]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_5216,plain,
% 2.59/1.00      ( m1_connsp_2(u1_struct_0(X0_53),X1_53,X0_54) = iProver_top
% 2.59/1.00      | v3_pre_topc(X1_54,X1_53) != iProver_top
% 2.59/1.00      | r2_hidden(X0_54,X1_54) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.59/1.00      | r1_tarski(X1_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X1_53))) != iProver_top
% 2.59/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.59/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(X1_53) != iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_3340,c_3335]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6447,plain,
% 2.59/1.00      ( m1_connsp_2(u1_struct_0(X0_53),sK4,X0_54) = iProver_top
% 2.59/1.00      | v3_pre_topc(sK6,sK4) != iProver_top
% 2.59/1.00      | r2_hidden(X0_54,sK6) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.59/1.00      | r1_tarski(sK6,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 2.59/1.00      | v2_struct_0(sK4) = iProver_top
% 2.59/1.00      | l1_pre_topc(sK4) != iProver_top
% 2.59/1.00      | v2_pre_topc(sK4) != iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_3350,c_5216]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_36,negated_conjecture,
% 2.59/1.00      ( v2_pre_topc(sK1) ),
% 2.59/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_39,plain,
% 2.59/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_35,negated_conjecture,
% 2.59/1.00      ( l1_pre_topc(sK1) ),
% 2.59/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_40,plain,
% 2.59/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_29,negated_conjecture,
% 2.59/1.00      ( ~ v2_struct_0(sK4) ),
% 2.59/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_46,plain,
% 2.59/1.00      ( v2_struct_0(sK4) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_28,negated_conjecture,
% 2.59/1.00      ( m1_pre_topc(sK4,sK1) ),
% 2.59/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_47,plain,
% 2.59/1.00      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_20,negated_conjecture,
% 2.59/1.00      ( v3_pre_topc(sK6,sK4) ),
% 2.59/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_55,plain,
% 2.59/1.00      ( v3_pre_topc(sK6,sK4) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3,plain,
% 2.59/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.59/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2532,plain,
% 2.59/1.00      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.59/1.00      | ~ l1_pre_topc(X1_53)
% 2.59/1.00      | l1_pre_topc(X0_53) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3723,plain,
% 2.59/1.00      ( ~ m1_pre_topc(X0_53,sK1)
% 2.59/1.00      | l1_pre_topc(X0_53)
% 2.59/1.00      | ~ l1_pre_topc(sK1) ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_2532]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3724,plain,
% 2.59/1.00      ( m1_pre_topc(X0_53,sK1) != iProver_top
% 2.59/1.00      | l1_pre_topc(X0_53) = iProver_top
% 2.59/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_3723]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3726,plain,
% 2.59/1.00      ( m1_pre_topc(sK4,sK1) != iProver_top
% 2.59/1.00      | l1_pre_topc(sK4) = iProver_top
% 2.59/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_3724]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2,plain,
% 2.59/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X1)
% 2.59/1.00      | v2_pre_topc(X0) ),
% 2.59/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2533,plain,
% 2.59/1.00      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.59/1.00      | ~ l1_pre_topc(X1_53)
% 2.59/1.00      | ~ v2_pre_topc(X1_53)
% 2.59/1.00      | v2_pre_topc(X0_53) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3756,plain,
% 2.59/1.00      ( ~ m1_pre_topc(X0_53,sK1)
% 2.59/1.00      | ~ l1_pre_topc(sK1)
% 2.59/1.00      | v2_pre_topc(X0_53)
% 2.59/1.00      | ~ v2_pre_topc(sK1) ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_2533]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3757,plain,
% 2.59/1.00      ( m1_pre_topc(X0_53,sK1) != iProver_top
% 2.59/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.59/1.00      | v2_pre_topc(X0_53) = iProver_top
% 2.59/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_3756]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3759,plain,
% 2.59/1.00      ( m1_pre_topc(sK4,sK1) != iProver_top
% 2.59/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.59/1.00      | v2_pre_topc(sK4) = iProver_top
% 2.59/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_3757]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6666,plain,
% 2.59/1.00      ( m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 2.59/1.00      | r1_tarski(sK6,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.59/1.00      | r2_hidden(X0_54,sK6) != iProver_top
% 2.59/1.00      | m1_connsp_2(u1_struct_0(X0_53),sK4,X0_54) = iProver_top ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_6447,c_39,c_40,c_46,c_47,c_55,c_3726,c_3759]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6667,plain,
% 2.59/1.00      ( m1_connsp_2(u1_struct_0(X0_53),sK4,X0_54) = iProver_top
% 2.59/1.00      | r2_hidden(X0_54,sK6) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.59/1.00      | r1_tarski(sK6,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top ),
% 2.59/1.00      inference(renaming,[status(thm)],[c_6666]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1,plain,
% 2.59/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.59/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2534,plain,
% 2.59/1.00      ( r1_tarski(X0_54,X1_54)
% 2.59/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3332,plain,
% 2.59/1.00      ( r1_tarski(X0_54,X1_54) = iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2534]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_4376,plain,
% 2.59/1.00      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.59/1.00      | r1_tarski(u1_struct_0(X0_53),u1_struct_0(X1_53)) = iProver_top
% 2.59/1.00      | l1_pre_topc(X1_53) != iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_3340,c_3332]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_16,negated_conjecture,
% 2.59/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK7)
% 2.59/1.00      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
% 2.59/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2522,negated_conjecture,
% 2.59/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK7)
% 2.59/1.00      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3344,plain,
% 2.59/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
% 2.59/1.00      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2522]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_17,negated_conjecture,
% 2.59/1.00      ( sK7 = sK8 ),
% 2.59/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2521,negated_conjecture,
% 2.59/1.00      ( sK7 = sK8 ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3423,plain,
% 2.59/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK8) = iProver_top
% 2.59/1.00      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) = iProver_top ),
% 2.59/1.00      inference(light_normalisation,[status(thm)],[c_3344,c_2521]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_13,plain,
% 2.59/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.59/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.59/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.59/1.00      | ~ m1_connsp_2(X6,X0,X3)
% 2.59/1.00      | ~ m1_pre_topc(X4,X5)
% 2.59/1.00      | ~ m1_pre_topc(X0,X5)
% 2.59/1.00      | ~ m1_pre_topc(X4,X0)
% 2.59/1.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.59/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.59/1.00      | ~ v1_funct_1(X2)
% 2.59/1.00      | v2_struct_0(X5)
% 2.59/1.00      | v2_struct_0(X1)
% 2.59/1.00      | v2_struct_0(X4)
% 2.59/1.00      | v2_struct_0(X0)
% 2.59/1.00      | ~ l1_pre_topc(X5)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X5)
% 2.59/1.00      | ~ v2_pre_topc(X1) ),
% 2.59/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_26,negated_conjecture,
% 2.59/1.00      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 2.59/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_707,plain,
% 2.59/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.59/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.59/1.00      | ~ m1_connsp_2(X6,X0,X3)
% 2.59/1.00      | ~ m1_pre_topc(X0,X5)
% 2.59/1.00      | ~ m1_pre_topc(X4,X0)
% 2.59/1.00      | ~ m1_pre_topc(X4,X5)
% 2.59/1.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.59/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.59/1.00      | ~ v1_funct_1(X2)
% 2.59/1.00      | v2_struct_0(X0)
% 2.59/1.00      | v2_struct_0(X1)
% 2.59/1.00      | v2_struct_0(X5)
% 2.59/1.00      | v2_struct_0(X4)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ l1_pre_topc(X5)
% 2.59/1.00      | ~ v2_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X5)
% 2.59/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.59/1.00      | sK5 != X2 ),
% 2.59/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_708,plain,
% 2.59/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.59/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.59/1.00      | ~ m1_connsp_2(X5,X3,X4)
% 2.59/1.00      | ~ m1_pre_topc(X3,X2)
% 2.59/1.00      | ~ m1_pre_topc(X0,X3)
% 2.59/1.00      | ~ m1_pre_topc(X0,X2)
% 2.59/1.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.59/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.59/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.59/1.00      | ~ v1_funct_1(sK5)
% 2.59/1.00      | v2_struct_0(X3)
% 2.59/1.00      | v2_struct_0(X1)
% 2.59/1.00      | v2_struct_0(X2)
% 2.59/1.00      | v2_struct_0(X0)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ l1_pre_topc(X2)
% 2.59/1.00      | ~ v2_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X2)
% 2.59/1.00      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.59/1.00      inference(unflattening,[status(thm)],[c_707]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_27,negated_conjecture,
% 2.59/1.00      ( v1_funct_1(sK5) ),
% 2.59/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_712,plain,
% 2.59/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.59/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.59/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.59/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.59/1.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_pre_topc(X0,X2)
% 2.59/1.00      | ~ m1_pre_topc(X0,X3)
% 2.59/1.00      | ~ m1_pre_topc(X3,X2)
% 2.59/1.00      | ~ m1_connsp_2(X5,X3,X4)
% 2.59/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.59/1.00      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.59/1.00      | v2_struct_0(X3)
% 2.59/1.00      | v2_struct_0(X1)
% 2.59/1.00      | v2_struct_0(X2)
% 2.59/1.00      | v2_struct_0(X0)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ l1_pre_topc(X2)
% 2.59/1.00      | ~ v2_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X2)
% 2.59/1.00      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_708,c_27]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_713,plain,
% 2.59/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.59/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.59/1.00      | ~ m1_connsp_2(X5,X3,X4)
% 2.59/1.00      | ~ m1_pre_topc(X3,X2)
% 2.59/1.00      | ~ m1_pre_topc(X0,X3)
% 2.59/1.00      | ~ m1_pre_topc(X0,X2)
% 2.59/1.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.59/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.59/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.59/1.00      | v2_struct_0(X0)
% 2.59/1.00      | v2_struct_0(X1)
% 2.59/1.00      | v2_struct_0(X2)
% 2.59/1.00      | v2_struct_0(X3)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ l1_pre_topc(X2)
% 2.59/1.00      | ~ v2_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X2)
% 2.59/1.00      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.59/1.00      inference(renaming,[status(thm)],[c_712]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_11,plain,
% 2.59/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.59/1.00      | ~ m1_pre_topc(X2,X0)
% 2.59/1.00      | m1_pre_topc(X2,X1)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X1) ),
% 2.59/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_760,plain,
% 2.59/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.59/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.59/1.00      | ~ m1_connsp_2(X5,X3,X4)
% 2.59/1.00      | ~ m1_pre_topc(X3,X2)
% 2.59/1.00      | ~ m1_pre_topc(X0,X3)
% 2.59/1.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.59/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.59/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.59/1.00      | v2_struct_0(X0)
% 2.59/1.00      | v2_struct_0(X1)
% 2.59/1.00      | v2_struct_0(X2)
% 2.59/1.00      | v2_struct_0(X3)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ l1_pre_topc(X2)
% 2.59/1.00      | ~ v2_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X2)
% 2.59/1.00      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.59/1.00      inference(forward_subsumption_resolution,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_713,c_11]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2501,plain,
% 2.59/1.00      ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK5),X0_54)
% 2.59/1.00      | r1_tmap_1(X3_53,X1_53,sK5,X0_54)
% 2.59/1.00      | ~ m1_connsp_2(X1_54,X3_53,X0_54)
% 2.59/1.00      | ~ m1_pre_topc(X3_53,X2_53)
% 2.59/1.00      | ~ m1_pre_topc(X0_53,X3_53)
% 2.59/1.00      | ~ r1_tarski(X1_54,u1_struct_0(X0_53))
% 2.59/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 2.59/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(X3_53))
% 2.59/1.00      | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X3_53)))
% 2.59/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
% 2.59/1.00      | v2_struct_0(X0_53)
% 2.59/1.00      | v2_struct_0(X1_53)
% 2.59/1.00      | v2_struct_0(X2_53)
% 2.59/1.00      | v2_struct_0(X3_53)
% 2.59/1.00      | ~ l1_pre_topc(X1_53)
% 2.59/1.00      | ~ l1_pre_topc(X2_53)
% 2.59/1.00      | ~ v2_pre_topc(X1_53)
% 2.59/1.00      | ~ v2_pre_topc(X2_53)
% 2.59/1.00      | u1_struct_0(X3_53) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(X1_53) != u1_struct_0(sK2) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_760]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3364,plain,
% 2.59/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(X1_53) != u1_struct_0(sK2)
% 2.59/1.00      | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK5),X0_54) != iProver_top
% 2.59/1.00      | r1_tmap_1(X0_53,X1_53,sK5,X0_54) = iProver_top
% 2.59/1.00      | m1_connsp_2(X1_54,X0_53,X0_54) != iProver_top
% 2.59/1.00      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 2.59/1.00      | r1_tarski(X1_54,u1_struct_0(X2_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X2_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.59/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.59/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X3_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.59/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.59/1.00      | l1_pre_topc(X3_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(X1_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(X3_53) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2501]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_4574,plain,
% 2.59/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.59/1.00      | r1_tmap_1(X1_53,sK2,k3_tmap_1(X2_53,sK2,X0_53,X1_53,sK5),X0_54) != iProver_top
% 2.59/1.00      | r1_tmap_1(X0_53,sK2,sK5,X0_54) = iProver_top
% 2.59/1.00      | m1_connsp_2(X1_54,X0_53,X0_54) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.59/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.59/1.00      | r1_tarski(X1_54,u1_struct_0(X1_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.59/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK2)))) != iProver_top
% 2.59/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.59/1.00      | v2_struct_0(sK2) = iProver_top
% 2.59/1.00      | l1_pre_topc(X2_53) != iProver_top
% 2.59/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.59/1.00      | v2_pre_topc(X2_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 2.59/1.00      inference(equality_resolution,[status(thm)],[c_3364]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_34,negated_conjecture,
% 2.59/1.00      ( ~ v2_struct_0(sK2) ),
% 2.59/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_41,plain,
% 2.59/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_33,negated_conjecture,
% 2.59/1.00      ( v2_pre_topc(sK2) ),
% 2.59/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_42,plain,
% 2.59/1.00      ( v2_pre_topc(sK2) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_32,negated_conjecture,
% 2.59/1.00      ( l1_pre_topc(sK2) ),
% 2.59/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_43,plain,
% 2.59/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3697,plain,
% 2.59/1.00      ( ~ r1_tmap_1(X0_53,sK2,k3_tmap_1(X1_53,sK2,X2_53,X0_53,sK5),X0_54)
% 2.59/1.00      | r1_tmap_1(X2_53,sK2,sK5,X0_54)
% 2.59/1.00      | ~ m1_connsp_2(X1_54,X2_53,X0_54)
% 2.59/1.00      | ~ m1_pre_topc(X2_53,X1_53)
% 2.59/1.00      | ~ m1_pre_topc(X0_53,X2_53)
% 2.59/1.00      | ~ r1_tarski(X1_54,u1_struct_0(X0_53))
% 2.59/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 2.59/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(X2_53))
% 2.59/1.00      | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X2_53)))
% 2.59/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(sK2))))
% 2.59/1.00      | v2_struct_0(X0_53)
% 2.59/1.00      | v2_struct_0(X1_53)
% 2.59/1.00      | v2_struct_0(X2_53)
% 2.59/1.00      | v2_struct_0(sK2)
% 2.59/1.00      | ~ l1_pre_topc(X1_53)
% 2.59/1.00      | ~ l1_pre_topc(sK2)
% 2.59/1.00      | ~ v2_pre_topc(X1_53)
% 2.59/1.00      | ~ v2_pre_topc(sK2)
% 2.59/1.00      | u1_struct_0(X2_53) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_2501]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3698,plain,
% 2.59/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.59/1.00      | r1_tmap_1(X1_53,sK2,k3_tmap_1(X2_53,sK2,X0_53,X1_53,sK5),X0_54) != iProver_top
% 2.59/1.00      | r1_tmap_1(X0_53,sK2,sK5,X0_54) = iProver_top
% 2.59/1.00      | m1_connsp_2(X1_54,X0_53,X0_54) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.59/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.59/1.00      | r1_tarski(X1_54,u1_struct_0(X1_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.59/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK2)))) != iProver_top
% 2.59/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.59/1.00      | v2_struct_0(sK2) = iProver_top
% 2.59/1.00      | l1_pre_topc(X2_53) != iProver_top
% 2.59/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.59/1.00      | v2_pre_topc(X2_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_3697]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2537,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3991,plain,
% 2.59/1.00      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_2537]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_5100,plain,
% 2.59/1.00      ( v2_pre_topc(X2_53) != iProver_top
% 2.59/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.59/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK2)))) != iProver_top
% 2.59/1.00      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | r1_tarski(X1_54,u1_struct_0(X1_53)) != iProver_top
% 2.59/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.59/1.00      | m1_connsp_2(X1_54,X0_53,X0_54) != iProver_top
% 2.59/1.00      | r1_tmap_1(X0_53,sK2,sK5,X0_54) = iProver_top
% 2.59/1.00      | r1_tmap_1(X1_53,sK2,k3_tmap_1(X2_53,sK2,X0_53,X1_53,sK5),X0_54) != iProver_top
% 2.59/1.00      | u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.59/1.00      | l1_pre_topc(X2_53) != iProver_top ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_4574,c_41,c_42,c_43,c_3698,c_3991]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_5101,plain,
% 2.59/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.59/1.00      | r1_tmap_1(X1_53,sK2,k3_tmap_1(X2_53,sK2,X0_53,X1_53,sK5),X0_54) != iProver_top
% 2.59/1.00      | r1_tmap_1(X0_53,sK2,sK5,X0_54) = iProver_top
% 2.59/1.00      | m1_connsp_2(X1_54,X0_53,X0_54) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.59/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.59/1.00      | r1_tarski(X1_54,u1_struct_0(X1_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.59/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK2)))) != iProver_top
% 2.59/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.59/1.00      | l1_pre_topc(X2_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(X2_53) != iProver_top ),
% 2.59/1.00      inference(renaming,[status(thm)],[c_5100]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_5122,plain,
% 2.59/1.00      ( r1_tmap_1(X0_53,sK2,k3_tmap_1(X1_53,sK2,sK4,X0_53,sK5),X0_54) != iProver_top
% 2.59/1.00      | r1_tmap_1(sK4,sK2,sK5,X0_54) = iProver_top
% 2.59/1.00      | m1_connsp_2(X1_54,sK4,X0_54) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.59/1.00      | m1_pre_topc(sK4,X1_53) != iProver_top
% 2.59/1.00      | r1_tarski(X1_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 2.59/1.00      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.59/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.59/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.59/1.00      | v2_struct_0(sK4) = iProver_top
% 2.59/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(X1_53) != iProver_top ),
% 2.59/1.00      inference(equality_resolution,[status(thm)],[c_5101]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_25,negated_conjecture,
% 2.59/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 2.59/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_50,plain,
% 2.59/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6321,plain,
% 2.59/1.00      ( v2_struct_0(X0_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.59/1.00      | r1_tmap_1(X0_53,sK2,k3_tmap_1(X1_53,sK2,sK4,X0_53,sK5),X0_54) != iProver_top
% 2.59/1.00      | r1_tmap_1(sK4,sK2,sK5,X0_54) = iProver_top
% 2.59/1.00      | m1_connsp_2(X1_54,sK4,X0_54) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.59/1.00      | m1_pre_topc(sK4,X1_53) != iProver_top
% 2.59/1.00      | r1_tarski(X1_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 2.59/1.00      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.59/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(X1_53) != iProver_top ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_5122,c_46,c_50]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6322,plain,
% 2.59/1.00      ( r1_tmap_1(X0_53,sK2,k3_tmap_1(X1_53,sK2,sK4,X0_53,sK5),X0_54) != iProver_top
% 2.59/1.00      | r1_tmap_1(sK4,sK2,sK5,X0_54) = iProver_top
% 2.59/1.00      | m1_connsp_2(X1_54,sK4,X0_54) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.59/1.00      | m1_pre_topc(sK4,X1_53) != iProver_top
% 2.59/1.00      | r1_tarski(X1_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 2.59/1.00      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.59/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.59/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(X1_53) != iProver_top ),
% 2.59/1.00      inference(renaming,[status(thm)],[c_6321]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6340,plain,
% 2.59/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK8) = iProver_top
% 2.59/1.00      | m1_connsp_2(X0_54,sK4,sK8) != iProver_top
% 2.59/1.00      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.59/1.00      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.59/1.00      | r1_tarski(X0_54,u1_struct_0(sK3)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.59/1.00      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 2.59/1.00      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 2.59/1.00      | v2_struct_0(sK1) = iProver_top
% 2.59/1.00      | v2_struct_0(sK3) = iProver_top
% 2.59/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.59/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_3423,c_6322]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_37,negated_conjecture,
% 2.59/1.00      ( ~ v2_struct_0(sK1) ),
% 2.59/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_38,plain,
% 2.59/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_31,negated_conjecture,
% 2.59/1.00      ( ~ v2_struct_0(sK3) ),
% 2.59/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_44,plain,
% 2.59/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_24,negated_conjecture,
% 2.59/1.00      ( m1_pre_topc(sK3,sK4) ),
% 2.59/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_51,plain,
% 2.59/1.00      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_21,negated_conjecture,
% 2.59/1.00      ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
% 2.59/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_54,plain,
% 2.59/1.00      ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_22,negated_conjecture,
% 2.59/1.00      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 2.59/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2516,negated_conjecture,
% 2.59/1.00      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3349,plain,
% 2.59/1.00      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2516]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3398,plain,
% 2.59/1.00      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 2.59/1.00      inference(light_normalisation,[status(thm)],[c_3349,c_2521]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_14,plain,
% 2.59/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.59/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.59/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.59/1.00      | ~ m1_connsp_2(X6,X0,X3)
% 2.59/1.00      | ~ m1_pre_topc(X4,X5)
% 2.59/1.00      | ~ m1_pre_topc(X0,X5)
% 2.59/1.00      | ~ m1_pre_topc(X4,X0)
% 2.59/1.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.59/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.59/1.00      | ~ v1_funct_1(X2)
% 2.59/1.00      | v2_struct_0(X5)
% 2.59/1.00      | v2_struct_0(X1)
% 2.59/1.00      | v2_struct_0(X4)
% 2.59/1.00      | v2_struct_0(X0)
% 2.59/1.00      | ~ l1_pre_topc(X5)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X5)
% 2.59/1.00      | ~ v2_pre_topc(X1) ),
% 2.59/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_12,plain,
% 2.59/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.59/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.59/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.59/1.00      | ~ m1_pre_topc(X0,X5)
% 2.59/1.00      | ~ m1_pre_topc(X4,X0)
% 2.59/1.00      | ~ m1_pre_topc(X4,X5)
% 2.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.59/1.00      | ~ v1_funct_1(X2)
% 2.59/1.00      | v2_struct_0(X5)
% 2.59/1.00      | v2_struct_0(X1)
% 2.59/1.00      | v2_struct_0(X0)
% 2.59/1.00      | v2_struct_0(X4)
% 2.59/1.00      | ~ l1_pre_topc(X5)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X5)
% 2.59/1.00      | ~ v2_pre_topc(X1) ),
% 2.59/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_196,plain,
% 2.59/1.00      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.59/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.59/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.59/1.00      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.59/1.00      | ~ m1_pre_topc(X4,X5)
% 2.59/1.00      | ~ m1_pre_topc(X0,X5)
% 2.59/1.00      | ~ m1_pre_topc(X4,X0)
% 2.59/1.00      | ~ v1_funct_1(X2)
% 2.59/1.00      | v2_struct_0(X5)
% 2.59/1.00      | v2_struct_0(X1)
% 2.59/1.00      | v2_struct_0(X4)
% 2.59/1.00      | v2_struct_0(X0)
% 2.59/1.00      | ~ l1_pre_topc(X5)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X5)
% 2.59/1.00      | ~ v2_pre_topc(X1) ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_14,c_12]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_197,plain,
% 2.59/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.59/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.59/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.59/1.00      | ~ m1_pre_topc(X0,X5)
% 2.59/1.00      | ~ m1_pre_topc(X4,X0)
% 2.59/1.00      | ~ m1_pre_topc(X4,X5)
% 2.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.59/1.00      | ~ v1_funct_1(X2)
% 2.59/1.00      | v2_struct_0(X0)
% 2.59/1.00      | v2_struct_0(X1)
% 2.59/1.00      | v2_struct_0(X5)
% 2.59/1.00      | v2_struct_0(X4)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ l1_pre_topc(X5)
% 2.59/1.00      | ~ v2_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X5) ),
% 2.59/1.00      inference(renaming,[status(thm)],[c_196]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_641,plain,
% 2.59/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.59/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.59/1.00      | ~ m1_pre_topc(X0,X5)
% 2.59/1.00      | ~ m1_pre_topc(X4,X0)
% 2.59/1.00      | ~ m1_pre_topc(X4,X5)
% 2.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.59/1.00      | ~ v1_funct_1(X2)
% 2.59/1.00      | v2_struct_0(X0)
% 2.59/1.00      | v2_struct_0(X1)
% 2.59/1.00      | v2_struct_0(X5)
% 2.59/1.00      | v2_struct_0(X4)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ l1_pre_topc(X5)
% 2.59/1.00      | ~ v2_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X5)
% 2.59/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.59/1.00      | sK5 != X2 ),
% 2.59/1.00      inference(resolution_lifted,[status(thm)],[c_197,c_26]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_642,plain,
% 2.59/1.00      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.59/1.00      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.59/1.00      | ~ m1_pre_topc(X3,X2)
% 2.59/1.00      | ~ m1_pre_topc(X0,X3)
% 2.59/1.00      | ~ m1_pre_topc(X0,X2)
% 2.59/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.59/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.59/1.00      | ~ v1_funct_1(sK5)
% 2.59/1.00      | v2_struct_0(X3)
% 2.59/1.00      | v2_struct_0(X1)
% 2.59/1.00      | v2_struct_0(X2)
% 2.59/1.00      | v2_struct_0(X0)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ l1_pre_topc(X2)
% 2.59/1.00      | ~ v2_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X2)
% 2.59/1.00      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.59/1.00      inference(unflattening,[status(thm)],[c_641]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_646,plain,
% 2.59/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.59/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.59/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_pre_topc(X0,X2)
% 2.59/1.00      | ~ m1_pre_topc(X0,X3)
% 2.59/1.00      | ~ m1_pre_topc(X3,X2)
% 2.59/1.00      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.59/1.00      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.59/1.00      | v2_struct_0(X3)
% 2.59/1.00      | v2_struct_0(X1)
% 2.59/1.00      | v2_struct_0(X2)
% 2.59/1.00      | v2_struct_0(X0)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ l1_pre_topc(X2)
% 2.59/1.00      | ~ v2_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X2)
% 2.59/1.00      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_642,c_27]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_647,plain,
% 2.59/1.00      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.59/1.00      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.59/1.00      | ~ m1_pre_topc(X3,X2)
% 2.59/1.00      | ~ m1_pre_topc(X0,X3)
% 2.59/1.00      | ~ m1_pre_topc(X0,X2)
% 2.59/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.59/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.59/1.00      | v2_struct_0(X0)
% 2.59/1.00      | v2_struct_0(X1)
% 2.59/1.00      | v2_struct_0(X2)
% 2.59/1.00      | v2_struct_0(X3)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ l1_pre_topc(X2)
% 2.59/1.00      | ~ v2_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X2)
% 2.59/1.00      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.59/1.00      inference(renaming,[status(thm)],[c_646]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_688,plain,
% 2.59/1.00      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.59/1.00      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.59/1.00      | ~ m1_pre_topc(X3,X2)
% 2.59/1.00      | ~ m1_pre_topc(X0,X3)
% 2.59/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.59/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.59/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.59/1.00      | v2_struct_0(X0)
% 2.59/1.00      | v2_struct_0(X1)
% 2.59/1.00      | v2_struct_0(X2)
% 2.59/1.00      | v2_struct_0(X3)
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | ~ l1_pre_topc(X2)
% 2.59/1.00      | ~ v2_pre_topc(X1)
% 2.59/1.00      | ~ v2_pre_topc(X2)
% 2.59/1.00      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.59/1.00      inference(forward_subsumption_resolution,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_647,c_11]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2502,plain,
% 2.59/1.00      ( r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK5),X0_54)
% 2.59/1.00      | ~ r1_tmap_1(X3_53,X1_53,sK5,X0_54)
% 2.59/1.00      | ~ m1_pre_topc(X3_53,X2_53)
% 2.59/1.00      | ~ m1_pre_topc(X0_53,X3_53)
% 2.59/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 2.59/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(X3_53))
% 2.59/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
% 2.59/1.00      | v2_struct_0(X0_53)
% 2.59/1.00      | v2_struct_0(X1_53)
% 2.59/1.00      | v2_struct_0(X2_53)
% 2.59/1.00      | v2_struct_0(X3_53)
% 2.59/1.00      | ~ l1_pre_topc(X1_53)
% 2.59/1.00      | ~ l1_pre_topc(X2_53)
% 2.59/1.00      | ~ v2_pre_topc(X1_53)
% 2.59/1.00      | ~ v2_pre_topc(X2_53)
% 2.59/1.00      | u1_struct_0(X3_53) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(X1_53) != u1_struct_0(sK2) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_688]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3363,plain,
% 2.59/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(X1_53) != u1_struct_0(sK2)
% 2.59/1.00      | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK5),X0_54) = iProver_top
% 2.59/1.00      | r1_tmap_1(X0_53,X1_53,sK5,X0_54) != iProver_top
% 2.59/1.00      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X2_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.59/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X3_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.59/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.59/1.00      | l1_pre_topc(X3_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(X1_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(X3_53) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2502]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_4549,plain,
% 2.59/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.59/1.00      | r1_tmap_1(X1_53,sK2,k3_tmap_1(X2_53,sK2,X0_53,X1_53,sK5),X0_54) = iProver_top
% 2.59/1.00      | r1_tmap_1(X0_53,sK2,sK5,X0_54) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.59/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK2)))) != iProver_top
% 2.59/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.59/1.00      | v2_struct_0(sK2) = iProver_top
% 2.59/1.00      | l1_pre_topc(X2_53) != iProver_top
% 2.59/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.59/1.00      | v2_pre_topc(X2_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 2.59/1.00      inference(equality_resolution,[status(thm)],[c_3363]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3687,plain,
% 2.59/1.00      ( r1_tmap_1(X0_53,sK2,k3_tmap_1(X1_53,sK2,X2_53,X0_53,sK5),X0_54)
% 2.59/1.00      | ~ r1_tmap_1(X2_53,sK2,sK5,X0_54)
% 2.59/1.00      | ~ m1_pre_topc(X2_53,X1_53)
% 2.59/1.00      | ~ m1_pre_topc(X0_53,X2_53)
% 2.59/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 2.59/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(X2_53))
% 2.59/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(sK2))))
% 2.59/1.00      | v2_struct_0(X0_53)
% 2.59/1.00      | v2_struct_0(X1_53)
% 2.59/1.00      | v2_struct_0(X2_53)
% 2.59/1.00      | v2_struct_0(sK2)
% 2.59/1.00      | ~ l1_pre_topc(X1_53)
% 2.59/1.00      | ~ l1_pre_topc(sK2)
% 2.59/1.00      | ~ v2_pre_topc(X1_53)
% 2.59/1.00      | ~ v2_pre_topc(sK2)
% 2.59/1.00      | u1_struct_0(X2_53) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_2502]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3688,plain,
% 2.59/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.59/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.59/1.00      | r1_tmap_1(X1_53,sK2,k3_tmap_1(X2_53,sK2,X0_53,X1_53,sK5),X0_54) = iProver_top
% 2.59/1.00      | r1_tmap_1(X0_53,sK2,sK5,X0_54) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.59/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK2)))) != iProver_top
% 2.59/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.59/1.00      | v2_struct_0(sK2) = iProver_top
% 2.59/1.00      | l1_pre_topc(X2_53) != iProver_top
% 2.59/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.59/1.00      | v2_pre_topc(X2_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_3687]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_5076,plain,
% 2.59/1.00      ( v2_pre_topc(X2_53) != iProver_top
% 2.59/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.59/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK2)))) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.59/1.00      | r1_tmap_1(X0_53,sK2,sK5,X0_54) != iProver_top
% 2.59/1.00      | r1_tmap_1(X1_53,sK2,k3_tmap_1(X2_53,sK2,X0_53,X1_53,sK5),X0_54) = iProver_top
% 2.59/1.00      | u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.59/1.00      | l1_pre_topc(X2_53) != iProver_top ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_4549,c_41,c_42,c_43]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_5077,plain,
% 2.59/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.59/1.00      | r1_tmap_1(X1_53,sK2,k3_tmap_1(X2_53,sK2,X0_53,X1_53,sK5),X0_54) = iProver_top
% 2.59/1.00      | r1_tmap_1(X0_53,sK2,sK5,X0_54) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.59/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK2)))) != iProver_top
% 2.59/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.59/1.00      | l1_pre_topc(X2_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(X2_53) != iProver_top ),
% 2.59/1.00      inference(renaming,[status(thm)],[c_5076]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_5095,plain,
% 2.59/1.00      ( r1_tmap_1(X0_53,sK2,k3_tmap_1(X1_53,sK2,sK4,X0_53,sK5),X0_54) = iProver_top
% 2.59/1.00      | r1_tmap_1(sK4,sK2,sK5,X0_54) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.59/1.00      | m1_pre_topc(sK4,X1_53) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 2.59/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.59/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.59/1.00      | v2_struct_0(sK4) = iProver_top
% 2.59/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(X1_53) != iProver_top ),
% 2.59/1.00      inference(equality_resolution,[status(thm)],[c_5077]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_5847,plain,
% 2.59/1.00      ( v2_struct_0(X0_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.59/1.00      | r1_tmap_1(X0_53,sK2,k3_tmap_1(X1_53,sK2,sK4,X0_53,sK5),X0_54) = iProver_top
% 2.59/1.00      | r1_tmap_1(sK4,sK2,sK5,X0_54) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.59/1.00      | m1_pre_topc(sK4,X1_53) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 2.59/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(X1_53) != iProver_top ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_5095,c_46,c_50]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_5848,plain,
% 2.59/1.00      ( r1_tmap_1(X0_53,sK2,k3_tmap_1(X1_53,sK2,sK4,X0_53,sK5),X0_54) = iProver_top
% 2.59/1.00      | r1_tmap_1(sK4,sK2,sK5,X0_54) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.59/1.00      | m1_pre_topc(sK4,X1_53) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 2.59/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.59/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.59/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(X1_53) != iProver_top ),
% 2.59/1.00      inference(renaming,[status(thm)],[c_5847]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_15,negated_conjecture,
% 2.59/1.00      ( ~ r1_tmap_1(sK4,sK2,sK5,sK7)
% 2.59/1.00      | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
% 2.59/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2523,negated_conjecture,
% 2.59/1.00      ( ~ r1_tmap_1(sK4,sK2,sK5,sK7)
% 2.59/1.00      | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3343,plain,
% 2.59/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
% 2.59/1.00      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2523]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3434,plain,
% 2.59/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
% 2.59/1.00      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top ),
% 2.59/1.00      inference(light_normalisation,[status(thm)],[c_3343,c_2521]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_5863,plain,
% 2.59/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
% 2.59/1.00      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.59/1.00      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.59/1.00      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 2.59/1.00      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 2.59/1.00      | v2_struct_0(sK1) = iProver_top
% 2.59/1.00      | v2_struct_0(sK3) = iProver_top
% 2.59/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.59/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_5848,c_3434]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6370,plain,
% 2.59/1.00      ( m1_connsp_2(X0_54,sK4,sK8) != iProver_top
% 2.59/1.00      | r1_tarski(X0_54,u1_struct_0(sK3)) != iProver_top
% 2.59/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_6340,c_38,c_39,c_40,c_44,c_47,c_51,c_54,c_3398,c_5863]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6380,plain,
% 2.59/1.00      ( m1_connsp_2(u1_struct_0(X0_53),sK4,sK8) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.59/1.00      | r1_tarski(u1_struct_0(X0_53),u1_struct_0(sK3)) != iProver_top
% 2.59/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_3340,c_6370]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6652,plain,
% 2.59/1.00      ( r1_tarski(u1_struct_0(X0_53),u1_struct_0(sK3)) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.59/1.00      | m1_connsp_2(u1_struct_0(X0_53),sK4,sK8) != iProver_top ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_6380,c_40,c_47,c_3726]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6653,plain,
% 2.59/1.00      ( m1_connsp_2(u1_struct_0(X0_53),sK4,sK8) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.59/1.00      | r1_tarski(u1_struct_0(X0_53),u1_struct_0(sK3)) != iProver_top ),
% 2.59/1.00      inference(renaming,[status(thm)],[c_6652]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6661,plain,
% 2.59/1.00      ( m1_connsp_2(u1_struct_0(X0_53),sK4,sK8) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.59/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_4376,c_6653]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2514,negated_conjecture,
% 2.59/1.00      ( m1_pre_topc(sK3,sK4) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3351,plain,
% 2.59/1.00      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2514]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3334,plain,
% 2.59/1.00      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.59/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.59/1.00      | l1_pre_topc(X0_53) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2532]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_4248,plain,
% 2.59/1.00      ( l1_pre_topc(sK4) != iProver_top
% 2.59/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_3351,c_3334]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2524,plain,
% 2.59/1.00      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.59/1.00      | ~ m1_pre_topc(X2_53,X0_53)
% 2.59/1.00      | m1_pre_topc(X2_53,X1_53)
% 2.59/1.00      | ~ l1_pre_topc(X1_53)
% 2.59/1.00      | ~ v2_pre_topc(X1_53) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3342,plain,
% 2.59/1.00      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.59/1.00      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 2.59/1.00      | m1_pre_topc(X2_53,X1_53) = iProver_top
% 2.59/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.59/1.00      | v2_pre_topc(X1_53) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2524]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_4685,plain,
% 2.59/1.00      ( m1_pre_topc(X0_53,sK4) = iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.59/1.00      | l1_pre_topc(sK4) != iProver_top
% 2.59/1.00      | v2_pre_topc(sK4) != iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_3351,c_3342]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_4922,plain,
% 2.59/1.00      ( m1_pre_topc(X0_53,sK4) = iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK3) != iProver_top ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_4685,c_39,c_40,c_47,c_3726,c_3759]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6722,plain,
% 2.59/1.00      ( m1_pre_topc(X0_53,sK3) != iProver_top
% 2.59/1.00      | m1_connsp_2(u1_struct_0(X0_53),sK4,sK8) != iProver_top ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_6661,c_40,c_47,c_3726,c_4248,c_4922]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6723,plain,
% 2.59/1.00      ( m1_connsp_2(u1_struct_0(X0_53),sK4,sK8) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK3) != iProver_top ),
% 2.59/1.00      inference(renaming,[status(thm)],[c_6722]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6730,plain,
% 2.59/1.00      ( r2_hidden(sK8,sK6) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.59/1.00      | r1_tarski(sK6,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_6667,c_6723]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_19,negated_conjecture,
% 2.59/1.00      ( r2_hidden(sK7,sK6) ),
% 2.59/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2519,negated_conjecture,
% 2.59/1.00      ( r2_hidden(sK7,sK6) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3346,plain,
% 2.59/1.00      ( r2_hidden(sK7,sK6) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2519]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3375,plain,
% 2.59/1.00      ( r2_hidden(sK8,sK6) = iProver_top ),
% 2.59/1.00      inference(light_normalisation,[status(thm)],[c_3346,c_2521]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6795,plain,
% 2.59/1.00      ( r1_tarski(sK6,u1_struct_0(X0_53)) != iProver_top
% 2.59/1.00      | m1_pre_topc(X0_53,sK3) != iProver_top ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_6730,c_3398,c_3375,c_4922]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6796,plain,
% 2.59/1.00      ( m1_pre_topc(X0_53,sK3) != iProver_top
% 2.59/1.00      | r1_tarski(sK6,u1_struct_0(X0_53)) != iProver_top ),
% 2.59/1.00      inference(renaming,[status(thm)],[c_6795]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6803,plain,
% 2.59/1.00      ( m1_pre_topc(sK3,sK3) != iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_3345,c_6796]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_10,plain,
% 2.59/1.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.59/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2525,plain,
% 2.59/1.00      ( m1_pre_topc(X0_53,X0_53) | ~ l1_pre_topc(X0_53) ),
% 2.59/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6187,plain,
% 2.59/1.00      ( m1_pre_topc(sK3,sK3) | ~ l1_pre_topc(sK3) ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_2525]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6190,plain,
% 2.59/1.00      ( m1_pre_topc(sK3,sK3) = iProver_top
% 2.59/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_6187]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(contradiction,plain,
% 2.59/1.00      ( $false ),
% 2.59/1.00      inference(minisat,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_6803,c_6190,c_4248,c_3726,c_47,c_40]) ).
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.59/1.00  
% 2.59/1.00  ------                               Statistics
% 2.59/1.00  
% 2.59/1.00  ------ General
% 2.59/1.00  
% 2.59/1.00  abstr_ref_over_cycles:                  0
% 2.59/1.00  abstr_ref_under_cycles:                 0
% 2.59/1.00  gc_basic_clause_elim:                   0
% 2.59/1.00  forced_gc_time:                         0
% 2.59/1.00  parsing_time:                           0.011
% 2.59/1.00  unif_index_cands_time:                  0.
% 2.59/1.00  unif_index_add_time:                    0.
% 2.59/1.00  orderings_time:                         0.
% 2.59/1.00  out_proof_time:                         0.015
% 2.59/1.00  total_time:                             0.234
% 2.59/1.00  num_of_symbols:                         58
% 2.59/1.00  num_of_terms:                           4597
% 2.59/1.00  
% 2.59/1.00  ------ Preprocessing
% 2.59/1.00  
% 2.59/1.00  num_of_splits:                          0
% 2.59/1.00  num_of_split_atoms:                     0
% 2.59/1.00  num_of_reused_defs:                     0
% 2.59/1.00  num_eq_ax_congr_red:                    31
% 2.59/1.00  num_of_sem_filtered_clauses:            1
% 2.59/1.00  num_of_subtypes:                        2
% 2.59/1.00  monotx_restored_types:                  0
% 2.59/1.00  sat_num_of_epr_types:                   0
% 2.59/1.00  sat_num_of_non_cyclic_types:            0
% 2.59/1.00  sat_guarded_non_collapsed_types:        0
% 2.59/1.00  num_pure_diseq_elim:                    0
% 2.59/1.00  simp_replaced_by:                       0
% 2.59/1.00  res_preprocessed:                       164
% 2.59/1.00  prep_upred:                             0
% 2.59/1.00  prep_unflattend:                        55
% 2.59/1.00  smt_new_axioms:                         0
% 2.59/1.00  pred_elim_cands:                        10
% 2.59/1.00  pred_elim:                              2
% 2.59/1.00  pred_elim_cl:                           3
% 2.59/1.00  pred_elim_cycles:                       10
% 2.59/1.00  merged_defs:                            16
% 2.59/1.00  merged_defs_ncl:                        0
% 2.59/1.00  bin_hyper_res:                          16
% 2.59/1.00  prep_cycles:                            4
% 2.59/1.00  pred_elim_time:                         0.053
% 2.59/1.00  splitting_time:                         0.
% 2.59/1.00  sem_filter_time:                        0.
% 2.59/1.00  monotx_time:                            0.
% 2.59/1.00  subtype_inf_time:                       0.
% 2.59/1.00  
% 2.59/1.00  ------ Problem properties
% 2.59/1.00  
% 2.59/1.00  clauses:                                35
% 2.59/1.00  conjectures:                            21
% 2.59/1.00  epr:                                    18
% 2.59/1.00  horn:                                   27
% 2.59/1.00  ground:                                 21
% 2.59/1.00  unary:                                  19
% 2.59/1.00  binary:                                 5
% 2.59/1.00  lits:                                   119
% 2.59/1.00  lits_eq:                                5
% 2.59/1.00  fd_pure:                                0
% 2.59/1.00  fd_pseudo:                              0
% 2.59/1.00  fd_cond:                                0
% 2.59/1.00  fd_pseudo_cond:                         0
% 2.59/1.00  ac_symbols:                             0
% 2.59/1.00  
% 2.59/1.00  ------ Propositional Solver
% 2.59/1.00  
% 2.59/1.00  prop_solver_calls:                      28
% 2.59/1.00  prop_fast_solver_calls:                 2311
% 2.59/1.00  smt_solver_calls:                       0
% 2.59/1.00  smt_fast_solver_calls:                  0
% 2.59/1.00  prop_num_of_clauses:                    1562
% 2.59/1.00  prop_preprocess_simplified:             5666
% 2.59/1.00  prop_fo_subsumed:                       112
% 2.59/1.00  prop_solver_time:                       0.
% 2.59/1.00  smt_solver_time:                        0.
% 2.59/1.00  smt_fast_solver_time:                   0.
% 2.59/1.00  prop_fast_solver_time:                  0.
% 2.59/1.00  prop_unsat_core_time:                   0.
% 2.59/1.00  
% 2.59/1.00  ------ QBF
% 2.59/1.00  
% 2.59/1.00  qbf_q_res:                              0
% 2.59/1.00  qbf_num_tautologies:                    0
% 2.59/1.00  qbf_prep_cycles:                        0
% 2.59/1.00  
% 2.59/1.00  ------ BMC1
% 2.59/1.00  
% 2.59/1.00  bmc1_current_bound:                     -1
% 2.59/1.00  bmc1_last_solved_bound:                 -1
% 2.59/1.00  bmc1_unsat_core_size:                   -1
% 2.59/1.00  bmc1_unsat_core_parents_size:           -1
% 2.59/1.00  bmc1_merge_next_fun:                    0
% 2.59/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.59/1.00  
% 2.59/1.00  ------ Instantiation
% 2.59/1.00  
% 2.59/1.00  inst_num_of_clauses:                    418
% 2.59/1.00  inst_num_in_passive:                    67
% 2.59/1.00  inst_num_in_active:                     318
% 2.59/1.00  inst_num_in_unprocessed:                33
% 2.59/1.00  inst_num_of_loops:                      390
% 2.59/1.00  inst_num_of_learning_restarts:          0
% 2.59/1.00  inst_num_moves_active_passive:          68
% 2.59/1.00  inst_lit_activity:                      0
% 2.59/1.00  inst_lit_activity_moves:                0
% 2.59/1.00  inst_num_tautologies:                   0
% 2.59/1.00  inst_num_prop_implied:                  0
% 2.59/1.00  inst_num_existing_simplified:           0
% 2.59/1.00  inst_num_eq_res_simplified:             0
% 2.59/1.00  inst_num_child_elim:                    0
% 2.59/1.00  inst_num_of_dismatching_blockings:      78
% 2.59/1.00  inst_num_of_non_proper_insts:           459
% 2.59/1.00  inst_num_of_duplicates:                 0
% 2.59/1.00  inst_inst_num_from_inst_to_res:         0
% 2.59/1.00  inst_dismatching_checking_time:         0.
% 2.59/1.00  
% 2.59/1.00  ------ Resolution
% 2.59/1.00  
% 2.59/1.00  res_num_of_clauses:                     0
% 2.59/1.00  res_num_in_passive:                     0
% 2.59/1.00  res_num_in_active:                      0
% 2.59/1.00  res_num_of_loops:                       168
% 2.59/1.00  res_forward_subset_subsumed:            78
% 2.59/1.00  res_backward_subset_subsumed:           0
% 2.59/1.00  res_forward_subsumed:                   0
% 2.59/1.00  res_backward_subsumed:                  0
% 2.59/1.00  res_forward_subsumption_resolution:     4
% 2.59/1.00  res_backward_subsumption_resolution:    0
% 2.59/1.00  res_clause_to_clause_subsumption:       573
% 2.59/1.00  res_orphan_elimination:                 0
% 2.59/1.00  res_tautology_del:                      115
% 2.59/1.00  res_num_eq_res_simplified:              0
% 2.59/1.00  res_num_sel_changes:                    0
% 2.59/1.00  res_moves_from_active_to_pass:          0
% 2.59/1.00  
% 2.59/1.00  ------ Superposition
% 2.59/1.00  
% 2.59/1.00  sup_time_total:                         0.
% 2.59/1.00  sup_time_generating:                    0.
% 2.59/1.00  sup_time_sim_full:                      0.
% 2.59/1.00  sup_time_sim_immed:                     0.
% 2.59/1.00  
% 2.59/1.00  sup_num_of_clauses:                     84
% 2.59/1.00  sup_num_in_active:                      76
% 2.59/1.00  sup_num_in_passive:                     8
% 2.59/1.00  sup_num_of_loops:                       76
% 2.59/1.00  sup_fw_superposition:                   60
% 2.59/1.00  sup_bw_superposition:                   5
% 2.59/1.00  sup_immediate_simplified:               5
% 2.59/1.00  sup_given_eliminated:                   0
% 2.59/1.00  comparisons_done:                       0
% 2.59/1.00  comparisons_avoided:                    0
% 2.59/1.00  
% 2.59/1.00  ------ Simplifications
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  sim_fw_subset_subsumed:                 4
% 2.59/1.00  sim_bw_subset_subsumed:                 2
% 2.59/1.00  sim_fw_subsumed:                        1
% 2.59/1.00  sim_bw_subsumed:                        0
% 2.59/1.00  sim_fw_subsumption_res:                 0
% 2.59/1.00  sim_bw_subsumption_res:                 0
% 2.59/1.00  sim_tautology_del:                      7
% 2.59/1.00  sim_eq_tautology_del:                   0
% 2.59/1.00  sim_eq_res_simp:                        0
% 2.59/1.00  sim_fw_demodulated:                     0
% 2.59/1.00  sim_bw_demodulated:                     0
% 2.59/1.00  sim_light_normalised:                   4
% 2.59/1.00  sim_joinable_taut:                      0
% 2.59/1.00  sim_joinable_simp:                      0
% 2.59/1.00  sim_ac_normalised:                      0
% 2.59/1.00  sim_smt_subsumption:                    0
% 2.59/1.00  
%------------------------------------------------------------------------------
