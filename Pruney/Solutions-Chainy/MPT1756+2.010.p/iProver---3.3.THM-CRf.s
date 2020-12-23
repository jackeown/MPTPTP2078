%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:38 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 887 expanded)
%              Number of clauses        :  110 ( 145 expanded)
%              Number of leaves         :   14 ( 379 expanded)
%              Depth                    :   31
%              Number of atoms          : 1299 (16942 expanded)
%              Number of equality atoms :  164 (1109 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   44 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
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

fof(f5,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f4])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                | ~ r1_tmap_1(X1,X0,X2,X5) )
                              & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                | r1_tmap_1(X1,X0,X2,X5) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                | ~ r1_tmap_1(X1,X0,X2,X5) )
                              & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                | r1_tmap_1(X1,X0,X2,X5) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
            | ~ r1_tmap_1(X1,X0,X2,X5) )
          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
            | r1_tmap_1(X1,X0,X2,X5) )
          & X5 = X6
          & r1_tarski(X4,u1_struct_0(X3))
          & r2_hidden(X5,X4)
          & v3_pre_topc(X4,X1)
          & m1_subset_1(X6,u1_struct_0(X3)) )
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK9)
          | ~ r1_tmap_1(X1,X0,X2,X5) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK9)
          | r1_tmap_1(X1,X0,X2,X5) )
        & sK9 = X5
        & r1_tarski(X4,u1_struct_0(X3))
        & r2_hidden(X5,X4)
        & v3_pre_topc(X4,X1)
        & m1_subset_1(sK9,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                | ~ r1_tmap_1(X1,X0,X2,X5) )
              & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                | r1_tmap_1(X1,X0,X2,X5) )
              & X5 = X6
              & r1_tarski(X4,u1_struct_0(X3))
              & r2_hidden(X5,X4)
              & v3_pre_topc(X4,X1)
              & m1_subset_1(X6,u1_struct_0(X3)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
              | ~ r1_tmap_1(X1,X0,X2,sK8) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
              | r1_tmap_1(X1,X0,X2,sK8) )
            & sK8 = X6
            & r1_tarski(X4,u1_struct_0(X3))
            & r2_hidden(sK8,X4)
            & v3_pre_topc(X4,X1)
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK8,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                    | ~ r1_tmap_1(X1,X0,X2,X5) )
                  & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                    | r1_tmap_1(X1,X0,X2,X5) )
                  & X5 = X6
                  & r1_tarski(X4,u1_struct_0(X3))
                  & r2_hidden(X5,X4)
                  & v3_pre_topc(X4,X1)
                  & m1_subset_1(X6,u1_struct_0(X3)) )
              & m1_subset_1(X5,u1_struct_0(X1)) )
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                  | ~ r1_tmap_1(X1,X0,X2,X5) )
                & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                  | r1_tmap_1(X1,X0,X2,X5) )
                & X5 = X6
                & r1_tarski(sK7,u1_struct_0(X3))
                & r2_hidden(X5,sK7)
                & v3_pre_topc(sK7,X1)
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                        | ~ r1_tmap_1(X1,X0,X2,X5) )
                      & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                        | r1_tmap_1(X1,X0,X2,X5) )
                      & X5 = X6
                      & r1_tarski(X4,u1_struct_0(X3))
                      & r2_hidden(X5,X4)
                      & v3_pre_topc(X4,X1)
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X3,X1)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(sK6,X0,k2_tmap_1(X1,X0,X2,sK6),X6)
                      | ~ r1_tmap_1(X1,X0,X2,X5) )
                    & ( r1_tmap_1(sK6,X0,k2_tmap_1(X1,X0,X2,sK6),X6)
                      | r1_tmap_1(X1,X0,X2,X5) )
                    & X5 = X6
                    & r1_tarski(X4,u1_struct_0(sK6))
                    & r2_hidden(X5,X4)
                    & v3_pre_topc(X4,X1)
                    & m1_subset_1(X6,u1_struct_0(sK6)) )
                & m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(sK6,X1)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                            | ~ r1_tmap_1(X1,X0,X2,X5) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                            | r1_tmap_1(X1,X0,X2,X5) )
                          & X5 = X6
                          & r1_tarski(X4,u1_struct_0(X3))
                          & r2_hidden(X5,X4)
                          & v3_pre_topc(X4,X1)
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_pre_topc(X3,X1)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK5,X3),X6)
                          | ~ r1_tmap_1(X1,X0,sK5,X5) )
                        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK5,X3),X6)
                          | r1_tmap_1(X1,X0,sK5,X5) )
                        & X5 = X6
                        & r1_tarski(X4,u1_struct_0(X3))
                        & r2_hidden(X5,X4)
                        & v3_pre_topc(X4,X1)
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                | ~ r1_tmap_1(X1,X0,X2,X5) )
                              & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                | r1_tmap_1(X1,X0,X2,X5) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(sK4,X0,X2,X3),X6)
                              | ~ r1_tmap_1(sK4,X0,X2,X5) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(sK4,X0,X2,X3),X6)
                              | r1_tmap_1(sK4,X0,X2,X5) )
                            & X5 = X6
                            & r1_tarski(X4,u1_struct_0(X3))
                            & r2_hidden(X5,X4)
                            & v3_pre_topc(X4,sK4)
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,u1_struct_0(sK4)) )
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) )
                & m1_pre_topc(X3,sK4)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK4)
        & v2_pre_topc(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | ~ r1_tmap_1(X1,X0,X2,X5) )
                                & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | r1_tmap_1(X1,X0,X2,X5) )
                                & X5 = X6
                                & r1_tarski(X4,u1_struct_0(X3))
                                & r2_hidden(X5,X4)
                                & v3_pre_topc(X4,X1)
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                    & m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
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
                              ( ( ~ r1_tmap_1(X3,sK3,k2_tmap_1(X1,sK3,X2,X3),X6)
                                | ~ r1_tmap_1(X1,sK3,X2,X5) )
                              & ( r1_tmap_1(X3,sK3,k2_tmap_1(X1,sK3,X2,X3),X6)
                                | r1_tmap_1(X1,sK3,X2,X5) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9)
      | ~ r1_tmap_1(sK4,sK3,sK5,sK8) )
    & ( r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9)
      | r1_tmap_1(sK4,sK3,sK5,sK8) )
    & sK8 = sK9
    & r1_tarski(sK7,u1_struct_0(sK6))
    & r2_hidden(sK8,sK7)
    & v3_pre_topc(sK7,sK4)
    & m1_subset_1(sK9,u1_struct_0(sK6))
    & m1_subset_1(sK8,u1_struct_0(sK4))
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))
    & m1_pre_topc(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f24,f31,f30,f29,f28,f27,f26,f25])).

fof(f55,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( r1_tarski(X3,X1)
                      & m1_connsp_2(X3,X0,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( r1_tarski(X5,X1)
                      & m1_connsp_2(X5,X0,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f17])).

fof(f20,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK2(X0,X1,X4),X1)
        & m1_connsp_2(sK2(X0,X1,X4),X0,X4)
        & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X1)
              | ~ m1_connsp_2(X3,X0,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_tarski(X3,X1)
            | ~ m1_connsp_2(X3,X0,sK1(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,sK1(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ( r1_tarski(sK2(X0,X1,X4),X1)
                    & m1_connsp_2(sK2(X0,X1,X4),X0,X4)
                    & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f20,f19])).

fof(f37,plain,(
    ! [X4,X0,X1] :
      ( m1_connsp_2(sK2(X0,X1,X4),X0,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f38,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(sK2(X0,X1,X4),X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,
    ( r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9)
    | r1_tmap_1(sK4,sK3,sK5,sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    sK8 = sK9 ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

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
    inference(nnf_transformation,[],[f10])).

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
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
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

fof(f54,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    m1_subset_1(sK9,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,
    ( ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9)
    | ~ r1_tmap_1(sK4,sK3,sK5,sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f32])).

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
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
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

fof(f59,plain,(
    r2_hidden(sK8,sK7) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    r1_tarski(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    v3_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_7282,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_8052,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7282])).

cnf(c_7,plain,
    ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v3_pre_topc(X1,X0)
    | ~ r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_818,plain,
    ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v3_pre_topc(X1,X0)
    | ~ r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_25])).

cnf(c_819,plain,
    ( m1_connsp_2(sK2(sK4,X0,X1),sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v3_pre_topc(X0,sK4)
    | ~ r2_hidden(X1,X0)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_818])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_823,plain,
    ( m1_connsp_2(sK2(sK4,X0,X1),sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v3_pre_topc(X0,sK4)
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_819,c_27,c_26])).

cnf(c_7278,plain,
    ( m1_connsp_2(sK2(sK4,X0_55,X1_55),sK4,X1_55)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK4))
    | ~ v3_pre_topc(X0_55,sK4)
    | ~ r2_hidden(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_823])).

cnf(c_8058,plain,
    ( m1_connsp_2(sK2(sK4,X0_55,X1_55),sK4,X1_55) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top
    | v3_pre_topc(X0_55,sK4) != iProver_top
    | r2_hidden(X1_55,X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7278])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r1_tarski(sK2(X1,X0,X2),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_971,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r1_tarski(sK2(X1,X0,X2),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_25])).

cnf(c_972,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v3_pre_topc(X0,sK4)
    | ~ r2_hidden(X1,X0)
    | r1_tarski(sK2(sK4,X0,X1),X0)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_971])).

cnf(c_976,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v3_pre_topc(X0,sK4)
    | ~ r2_hidden(X1,X0)
    | r1_tarski(sK2(sK4,X0,X1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_972,c_27,c_26])).

cnf(c_7275,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK4))
    | ~ v3_pre_topc(X0_55,sK4)
    | ~ r2_hidden(X1_55,X0_55)
    | r1_tarski(sK2(sK4,X0_55,X1_55),X0_55) ),
    inference(subtyping,[status(esa)],[c_976])).

cnf(c_8061,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top
    | v3_pre_topc(X0_55,sK4) != iProver_top
    | r2_hidden(X1_55,X0_55) != iProver_top
    | r1_tarski(sK2(sK4,X0_55,X1_55),X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7275])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_7292,plain,
    ( r2_hidden(sK0(X0_55,X1_55),X0_55)
    | r1_tarski(X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_8043,plain,
    ( r2_hidden(sK0(X0_55,X1_55),X0_55) = iProver_top
    | r1_tarski(X0_55,X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7292])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_7291,plain,
    ( ~ r2_hidden(X0_55,X1_55)
    | r2_hidden(X0_55,X2_55)
    | ~ r1_tarski(X1_55,X2_55) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_8044,plain,
    ( r2_hidden(X0_55,X1_55) != iProver_top
    | r2_hidden(X0_55,X2_55) = iProver_top
    | r1_tarski(X1_55,X2_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7291])).

cnf(c_8564,plain,
    ( r2_hidden(sK0(X0_55,X1_55),X2_55) = iProver_top
    | r1_tarski(X0_55,X2_55) != iProver_top
    | r1_tarski(X0_55,X1_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_8043,c_8044])).

cnf(c_8914,plain,
    ( r2_hidden(sK0(X0_55,X1_55),X2_55) = iProver_top
    | r1_tarski(X0_55,X3_55) != iProver_top
    | r1_tarski(X3_55,X2_55) != iProver_top
    | r1_tarski(X0_55,X1_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_8564,c_8044])).

cnf(c_8977,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top
    | v3_pre_topc(X0_55,sK4) != iProver_top
    | r2_hidden(X1_55,X0_55) != iProver_top
    | r2_hidden(sK0(sK2(sK4,X0_55,X1_55),X2_55),X3_55) = iProver_top
    | r1_tarski(X0_55,X3_55) != iProver_top
    | r1_tarski(sK2(sK4,X0_55,X1_55),X2_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_8061,c_8914])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7293,plain,
    ( ~ r2_hidden(sK0(X0_55,X1_55),X1_55)
    | r1_tarski(X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_8042,plain,
    ( r2_hidden(sK0(X0_55,X1_55),X1_55) != iProver_top
    | r1_tarski(X0_55,X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7293])).

cnf(c_10519,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top
    | v3_pre_topc(X0_55,sK4) != iProver_top
    | r2_hidden(X1_55,X0_55) != iProver_top
    | r1_tarski(X0_55,X2_55) != iProver_top
    | r1_tarski(sK2(sK4,X0_55,X1_55),X2_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_8977,c_8042])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_944,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_945,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(X0,sK4)
    | ~ r2_hidden(X1,X0)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_944])).

cnf(c_949,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(X0,sK4)
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_945,c_27,c_26])).

cnf(c_7276,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X0_55,X1_55),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(X0_55,sK4)
    | ~ r2_hidden(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_949])).

cnf(c_8060,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2(sK4,X0_55,X1_55),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v3_pre_topc(X0_55,sK4) != iProver_top
    | r2_hidden(X1_55,X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7276])).

cnf(c_12,negated_conjecture,
    ( r1_tmap_1(sK4,sK3,sK5,sK8)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_7289,negated_conjecture,
    ( r1_tmap_1(sK4,sK3,sK5,sK8)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_8046,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK8) = iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7289])).

cnf(c_13,negated_conjecture,
    ( sK8 = sK9 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_7288,negated_conjecture,
    ( sK8 = sK9 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_8104,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK9) = iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8046,c_7288])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_9,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_437,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK6 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_438,plain,
    ( r1_tmap_1(sK4,X0,X1,X2)
    | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ r1_tarski(X3,u1_struct_0(sK6))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_442,plain,
    ( ~ l1_pre_topc(X0)
    | r1_tmap_1(sK4,X0,X1,X2)
    | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ r1_tarski(X3,u1_struct_0(sK6))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_27,c_26,c_25,c_21])).

cnf(c_443,plain,
    ( r1_tmap_1(sK4,X0,X1,X2)
    | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ r1_tarski(X3,u1_struct_0(sK6))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_442])).

cnf(c_490,plain,
    ( r1_tmap_1(sK4,X0,X1,X2)
    | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
    | ~ m1_connsp_2(X3,sK4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ r1_tarski(X3,u1_struct_0(sK6))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_443])).

cnf(c_491,plain,
    ( r1_tmap_1(sK4,X0,sK5,X1)
    | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_connsp_2(X2,sK4,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK6))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_495,plain,
    ( ~ r1_tarski(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_connsp_2(X2,sK4,X1)
    | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | r1_tmap_1(sK4,X0,sK5,X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_24])).

cnf(c_496,plain,
    ( r1_tmap_1(sK4,X0,sK5,X1)
    | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_connsp_2(X2,sK4,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_495])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_881,plain,
    ( r1_tmap_1(sK4,X0,sK5,X1)
    | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_connsp_2(X2,sK4,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_496,c_28])).

cnf(c_882,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | ~ m1_connsp_2(X1,sK4,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ r1_tarski(X1,u1_struct_0(sK6))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_881])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_886,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_connsp_2(X1,sK4,X0)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | r1_tmap_1(sK4,sK3,sK5,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK6))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_882,c_30,c_29,c_22])).

cnf(c_887,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | ~ m1_connsp_2(X1,sK4,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r1_tarski(X1,u1_struct_0(sK6))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_886])).

cnf(c_4279,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | ~ m1_connsp_2(X1,sK4,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r1_tarski(X1,u1_struct_0(sK6)) ),
    inference(equality_resolution_simp,[status(thm)],[c_887])).

cnf(c_7266,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0_55)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55)
    | ~ m1_connsp_2(X1_55,sK4,X0_55)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | ~ r1_tarski(X1_55,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_4279])).

cnf(c_8070,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0_55) = iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55) != iProver_top
    | m1_connsp_2(X1_55,sK4,X0_55) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top
    | r1_tarski(X1_55,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7266])).

cnf(c_9634,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK9) = iProver_top
    | m1_connsp_2(X0_55,sK4,sK9) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
    | r1_tarski(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8104,c_8070])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_44,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK3,sK5,sK8)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_7290,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK3,sK5,sK8)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_8045,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK8) != iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7290])).

cnf(c_8109,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK9) != iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8045,c_7288])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_7283,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_8051,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7283])).

cnf(c_8083,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8051,c_7288])).

cnf(c_10,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_386,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK6 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_387,plain,
    ( ~ r1_tmap_1(sK4,X0,X1,X2)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ r1_tarski(X3,u1_struct_0(sK6))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_391,plain,
    ( ~ l1_pre_topc(X0)
    | ~ r1_tmap_1(sK4,X0,X1,X2)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ r1_tarski(X3,u1_struct_0(sK6))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_27,c_26,c_25,c_21])).

cnf(c_392,plain,
    ( ~ r1_tmap_1(sK4,X0,X1,X2)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ r1_tarski(X3,u1_struct_0(sK6))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_391])).

cnf(c_538,plain,
    ( ~ r1_tmap_1(sK4,X0,X1,X2)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
    | ~ m1_connsp_2(X3,sK4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ r1_tarski(X3,u1_struct_0(sK6))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_392])).

cnf(c_539,plain,
    ( ~ r1_tmap_1(sK4,X0,sK5,X1)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_connsp_2(X2,sK4,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK6))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_543,plain,
    ( ~ r1_tarski(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_connsp_2(X2,sK4,X1)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ r1_tmap_1(sK4,X0,sK5,X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_539,c_24])).

cnf(c_544,plain,
    ( ~ r1_tmap_1(sK4,X0,sK5,X1)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_connsp_2(X2,sK4,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_543])).

cnf(c_845,plain,
    ( ~ r1_tmap_1(sK4,X0,sK5,X1)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_connsp_2(X2,sK4,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_544,c_28])).

cnf(c_846,plain,
    ( ~ r1_tmap_1(sK4,sK3,sK5,X0)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | ~ m1_connsp_2(X1,sK4,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ r1_tarski(X1,u1_struct_0(sK6))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_845])).

cnf(c_850,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_connsp_2(X1,sK4,X0)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | ~ r1_tmap_1(sK4,sK3,sK5,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK6))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_846,c_30,c_29,c_22])).

cnf(c_851,plain,
    ( ~ r1_tmap_1(sK4,sK3,sK5,X0)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | ~ m1_connsp_2(X1,sK4,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r1_tarski(X1,u1_struct_0(sK6))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_850])).

cnf(c_4283,plain,
    ( ~ r1_tmap_1(sK4,sK3,sK5,X0)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | ~ m1_connsp_2(X1,sK4,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r1_tarski(X1,u1_struct_0(sK6)) ),
    inference(equality_resolution_simp,[status(thm)],[c_851])).

cnf(c_7265,plain,
    ( ~ r1_tmap_1(sK4,sK3,sK5,X0_55)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55)
    | ~ m1_connsp_2(X1_55,sK4,X0_55)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | ~ r1_tarski(X1_55,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_4283])).

cnf(c_9652,plain,
    ( ~ r1_tmap_1(sK4,sK3,sK5,sK9)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9)
    | ~ m1_connsp_2(X0_55,sK4,sK9)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK4))
    | ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ r1_tarski(X0_55,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_7265])).

cnf(c_9653,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK9) != iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) = iProver_top
    | m1_connsp_2(X0_55,sK4,sK9) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
    | r1_tarski(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9652])).

cnf(c_9712,plain,
    ( m1_connsp_2(X0_55,sK4,sK9) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9634,c_44,c_8109,c_8083,c_9653])).

cnf(c_9722,plain,
    ( m1_connsp_2(sK2(sK4,X0_55,X1_55),sK4,sK9) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top
    | v3_pre_topc(X0_55,sK4) != iProver_top
    | r2_hidden(X1_55,X0_55) != iProver_top
    | r1_tarski(sK2(sK4,X0_55,X1_55),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8060,c_9712])).

cnf(c_10613,plain,
    ( m1_connsp_2(sK2(sK4,X0_55,X1_55),sK4,sK9) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top
    | v3_pre_topc(X0_55,sK4) != iProver_top
    | r2_hidden(X1_55,X0_55) != iProver_top
    | r1_tarski(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10519,c_9722])).

cnf(c_11898,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK4)) != iProver_top
    | v3_pre_topc(X0_55,sK4) != iProver_top
    | r2_hidden(sK9,X0_55) != iProver_top
    | r1_tarski(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8058,c_10613])).

cnf(c_11903,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v3_pre_topc(X0_55,sK4) != iProver_top
    | r2_hidden(sK9,X0_55) != iProver_top
    | r1_tarski(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11898,c_8083])).

cnf(c_11913,plain,
    ( v3_pre_topc(sK7,sK4) != iProver_top
    | r2_hidden(sK9,sK7) != iProver_top
    | r1_tarski(sK7,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8052,c_11903])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK8,sK7) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_7286,negated_conjecture,
    ( r2_hidden(sK8,sK7) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_8048,plain,
    ( r2_hidden(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7286])).

cnf(c_8074,plain,
    ( r2_hidden(sK9,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8048,c_7288])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_47,plain,
    ( r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16,negated_conjecture,
    ( v3_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_45,plain,
    ( v3_pre_topc(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11913,c_8074,c_47,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:13:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.88/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/0.98  
% 2.88/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.88/0.98  
% 2.88/0.98  ------  iProver source info
% 2.88/0.98  
% 2.88/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.88/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.88/0.98  git: non_committed_changes: false
% 2.88/0.98  git: last_make_outside_of_git: false
% 2.88/0.98  
% 2.88/0.98  ------ 
% 2.88/0.98  
% 2.88/0.98  ------ Input Options
% 2.88/0.98  
% 2.88/0.98  --out_options                           all
% 2.88/0.98  --tptp_safe_out                         true
% 2.88/0.98  --problem_path                          ""
% 2.88/0.98  --include_path                          ""
% 2.88/0.98  --clausifier                            res/vclausify_rel
% 2.88/0.98  --clausifier_options                    --mode clausify
% 2.88/0.98  --stdin                                 false
% 2.88/0.98  --stats_out                             all
% 2.88/0.98  
% 2.88/0.98  ------ General Options
% 2.88/0.98  
% 2.88/0.98  --fof                                   false
% 2.88/0.98  --time_out_real                         305.
% 2.88/0.98  --time_out_virtual                      -1.
% 2.88/0.98  --symbol_type_check                     false
% 2.88/0.98  --clausify_out                          false
% 2.88/0.98  --sig_cnt_out                           false
% 2.88/0.99  --trig_cnt_out                          false
% 2.88/0.99  --trig_cnt_out_tolerance                1.
% 2.88/0.99  --trig_cnt_out_sk_spl                   false
% 2.88/0.99  --abstr_cl_out                          false
% 2.88/0.99  
% 2.88/0.99  ------ Global Options
% 2.88/0.99  
% 2.88/0.99  --schedule                              default
% 2.88/0.99  --add_important_lit                     false
% 2.88/0.99  --prop_solver_per_cl                    1000
% 2.88/0.99  --min_unsat_core                        false
% 2.88/0.99  --soft_assumptions                      false
% 2.88/0.99  --soft_lemma_size                       3
% 2.88/0.99  --prop_impl_unit_size                   0
% 2.88/0.99  --prop_impl_unit                        []
% 2.88/0.99  --share_sel_clauses                     true
% 2.88/0.99  --reset_solvers                         false
% 2.88/0.99  --bc_imp_inh                            [conj_cone]
% 2.88/0.99  --conj_cone_tolerance                   3.
% 2.88/0.99  --extra_neg_conj                        none
% 2.88/0.99  --large_theory_mode                     true
% 2.88/0.99  --prolific_symb_bound                   200
% 2.88/0.99  --lt_threshold                          2000
% 2.88/0.99  --clause_weak_htbl                      true
% 2.88/0.99  --gc_record_bc_elim                     false
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing Options
% 2.88/0.99  
% 2.88/0.99  --preprocessing_flag                    true
% 2.88/0.99  --time_out_prep_mult                    0.1
% 2.88/0.99  --splitting_mode                        input
% 2.88/0.99  --splitting_grd                         true
% 2.88/0.99  --splitting_cvd                         false
% 2.88/0.99  --splitting_cvd_svl                     false
% 2.88/0.99  --splitting_nvd                         32
% 2.88/0.99  --sub_typing                            true
% 2.88/0.99  --prep_gs_sim                           true
% 2.88/0.99  --prep_unflatten                        true
% 2.88/0.99  --prep_res_sim                          true
% 2.88/0.99  --prep_upred                            true
% 2.88/0.99  --prep_sem_filter                       exhaustive
% 2.88/0.99  --prep_sem_filter_out                   false
% 2.88/0.99  --pred_elim                             true
% 2.88/0.99  --res_sim_input                         true
% 2.88/0.99  --eq_ax_congr_red                       true
% 2.88/0.99  --pure_diseq_elim                       true
% 2.88/0.99  --brand_transform                       false
% 2.88/0.99  --non_eq_to_eq                          false
% 2.88/0.99  --prep_def_merge                        true
% 2.88/0.99  --prep_def_merge_prop_impl              false
% 2.88/0.99  --prep_def_merge_mbd                    true
% 2.88/0.99  --prep_def_merge_tr_red                 false
% 2.88/0.99  --prep_def_merge_tr_cl                  false
% 2.88/0.99  --smt_preprocessing                     true
% 2.88/0.99  --smt_ac_axioms                         fast
% 2.88/0.99  --preprocessed_out                      false
% 2.88/0.99  --preprocessed_stats                    false
% 2.88/0.99  
% 2.88/0.99  ------ Abstraction refinement Options
% 2.88/0.99  
% 2.88/0.99  --abstr_ref                             []
% 2.88/0.99  --abstr_ref_prep                        false
% 2.88/0.99  --abstr_ref_until_sat                   false
% 2.88/0.99  --abstr_ref_sig_restrict                funpre
% 2.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/0.99  --abstr_ref_under                       []
% 2.88/0.99  
% 2.88/0.99  ------ SAT Options
% 2.88/0.99  
% 2.88/0.99  --sat_mode                              false
% 2.88/0.99  --sat_fm_restart_options                ""
% 2.88/0.99  --sat_gr_def                            false
% 2.88/0.99  --sat_epr_types                         true
% 2.88/0.99  --sat_non_cyclic_types                  false
% 2.88/0.99  --sat_finite_models                     false
% 2.88/0.99  --sat_fm_lemmas                         false
% 2.88/0.99  --sat_fm_prep                           false
% 2.88/0.99  --sat_fm_uc_incr                        true
% 2.88/0.99  --sat_out_model                         small
% 2.88/0.99  --sat_out_clauses                       false
% 2.88/0.99  
% 2.88/0.99  ------ QBF Options
% 2.88/0.99  
% 2.88/0.99  --qbf_mode                              false
% 2.88/0.99  --qbf_elim_univ                         false
% 2.88/0.99  --qbf_dom_inst                          none
% 2.88/0.99  --qbf_dom_pre_inst                      false
% 2.88/0.99  --qbf_sk_in                             false
% 2.88/0.99  --qbf_pred_elim                         true
% 2.88/0.99  --qbf_split                             512
% 2.88/0.99  
% 2.88/0.99  ------ BMC1 Options
% 2.88/0.99  
% 2.88/0.99  --bmc1_incremental                      false
% 2.88/0.99  --bmc1_axioms                           reachable_all
% 2.88/0.99  --bmc1_min_bound                        0
% 2.88/0.99  --bmc1_max_bound                        -1
% 2.88/0.99  --bmc1_max_bound_default                -1
% 2.88/0.99  --bmc1_symbol_reachability              true
% 2.88/0.99  --bmc1_property_lemmas                  false
% 2.88/0.99  --bmc1_k_induction                      false
% 2.88/0.99  --bmc1_non_equiv_states                 false
% 2.88/0.99  --bmc1_deadlock                         false
% 2.88/0.99  --bmc1_ucm                              false
% 2.88/0.99  --bmc1_add_unsat_core                   none
% 2.88/0.99  --bmc1_unsat_core_children              false
% 2.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/0.99  --bmc1_out_stat                         full
% 2.88/0.99  --bmc1_ground_init                      false
% 2.88/0.99  --bmc1_pre_inst_next_state              false
% 2.88/0.99  --bmc1_pre_inst_state                   false
% 2.88/0.99  --bmc1_pre_inst_reach_state             false
% 2.88/0.99  --bmc1_out_unsat_core                   false
% 2.88/0.99  --bmc1_aig_witness_out                  false
% 2.88/0.99  --bmc1_verbose                          false
% 2.88/0.99  --bmc1_dump_clauses_tptp                false
% 2.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.88/0.99  --bmc1_dump_file                        -
% 2.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.88/0.99  --bmc1_ucm_extend_mode                  1
% 2.88/0.99  --bmc1_ucm_init_mode                    2
% 2.88/0.99  --bmc1_ucm_cone_mode                    none
% 2.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.88/0.99  --bmc1_ucm_relax_model                  4
% 2.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/0.99  --bmc1_ucm_layered_model                none
% 2.88/0.99  --bmc1_ucm_max_lemma_size               10
% 2.88/0.99  
% 2.88/0.99  ------ AIG Options
% 2.88/0.99  
% 2.88/0.99  --aig_mode                              false
% 2.88/0.99  
% 2.88/0.99  ------ Instantiation Options
% 2.88/0.99  
% 2.88/0.99  --instantiation_flag                    true
% 2.88/0.99  --inst_sos_flag                         false
% 2.88/0.99  --inst_sos_phase                        true
% 2.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel_side                     num_symb
% 2.88/0.99  --inst_solver_per_active                1400
% 2.88/0.99  --inst_solver_calls_frac                1.
% 2.88/0.99  --inst_passive_queue_type               priority_queues
% 2.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/0.99  --inst_passive_queues_freq              [25;2]
% 2.88/0.99  --inst_dismatching                      true
% 2.88/0.99  --inst_eager_unprocessed_to_passive     true
% 2.88/0.99  --inst_prop_sim_given                   true
% 2.88/0.99  --inst_prop_sim_new                     false
% 2.88/0.99  --inst_subs_new                         false
% 2.88/0.99  --inst_eq_res_simp                      false
% 2.88/0.99  --inst_subs_given                       false
% 2.88/0.99  --inst_orphan_elimination               true
% 2.88/0.99  --inst_learning_loop_flag               true
% 2.88/0.99  --inst_learning_start                   3000
% 2.88/0.99  --inst_learning_factor                  2
% 2.88/0.99  --inst_start_prop_sim_after_learn       3
% 2.88/0.99  --inst_sel_renew                        solver
% 2.88/0.99  --inst_lit_activity_flag                true
% 2.88/0.99  --inst_restr_to_given                   false
% 2.88/0.99  --inst_activity_threshold               500
% 2.88/0.99  --inst_out_proof                        true
% 2.88/0.99  
% 2.88/0.99  ------ Resolution Options
% 2.88/0.99  
% 2.88/0.99  --resolution_flag                       true
% 2.88/0.99  --res_lit_sel                           adaptive
% 2.88/0.99  --res_lit_sel_side                      none
% 2.88/0.99  --res_ordering                          kbo
% 2.88/0.99  --res_to_prop_solver                    active
% 2.88/0.99  --res_prop_simpl_new                    false
% 2.88/0.99  --res_prop_simpl_given                  true
% 2.88/0.99  --res_passive_queue_type                priority_queues
% 2.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/0.99  --res_passive_queues_freq               [15;5]
% 2.88/0.99  --res_forward_subs                      full
% 2.88/0.99  --res_backward_subs                     full
% 2.88/0.99  --res_forward_subs_resolution           true
% 2.88/0.99  --res_backward_subs_resolution          true
% 2.88/0.99  --res_orphan_elimination                true
% 2.88/0.99  --res_time_limit                        2.
% 2.88/0.99  --res_out_proof                         true
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Options
% 2.88/0.99  
% 2.88/0.99  --superposition_flag                    true
% 2.88/0.99  --sup_passive_queue_type                priority_queues
% 2.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.88/0.99  --demod_completeness_check              fast
% 2.88/0.99  --demod_use_ground                      true
% 2.88/0.99  --sup_to_prop_solver                    passive
% 2.88/0.99  --sup_prop_simpl_new                    true
% 2.88/0.99  --sup_prop_simpl_given                  true
% 2.88/0.99  --sup_fun_splitting                     false
% 2.88/0.99  --sup_smt_interval                      50000
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Simplification Setup
% 2.88/0.99  
% 2.88/0.99  --sup_indices_passive                   []
% 2.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_full_bw                           [BwDemod]
% 2.88/0.99  --sup_immed_triv                        [TrivRules]
% 2.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_immed_bw_main                     []
% 2.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  
% 2.88/0.99  ------ Combination Options
% 2.88/0.99  
% 2.88/0.99  --comb_res_mult                         3
% 2.88/0.99  --comb_sup_mult                         2
% 2.88/0.99  --comb_inst_mult                        10
% 2.88/0.99  
% 2.88/0.99  ------ Debug Options
% 2.88/0.99  
% 2.88/0.99  --dbg_backtrace                         false
% 2.88/0.99  --dbg_dump_prop_clauses                 false
% 2.88/0.99  --dbg_dump_prop_clauses_file            -
% 2.88/0.99  --dbg_out_stat                          false
% 2.88/0.99  ------ Parsing...
% 2.88/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.88/0.99  ------ Proving...
% 2.88/0.99  ------ Problem Properties 
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  clauses                                 31
% 2.88/0.99  conjectures                             10
% 2.88/0.99  EPR                                     4
% 2.88/0.99  Horn                                    25
% 2.88/0.99  unary                                   8
% 2.88/0.99  binary                                  4
% 2.88/0.99  lits                                    107
% 2.88/0.99  lits eq                                 3
% 2.88/0.99  fd_pure                                 0
% 2.88/0.99  fd_pseudo                               0
% 2.88/0.99  fd_cond                                 0
% 2.88/0.99  fd_pseudo_cond                          0
% 2.88/0.99  AC symbols                              0
% 2.88/0.99  
% 2.88/0.99  ------ Schedule dynamic 5 is on 
% 2.88/0.99  
% 2.88/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  ------ 
% 2.88/0.99  Current options:
% 2.88/0.99  ------ 
% 2.88/0.99  
% 2.88/0.99  ------ Input Options
% 2.88/0.99  
% 2.88/0.99  --out_options                           all
% 2.88/0.99  --tptp_safe_out                         true
% 2.88/0.99  --problem_path                          ""
% 2.88/0.99  --include_path                          ""
% 2.88/0.99  --clausifier                            res/vclausify_rel
% 2.88/0.99  --clausifier_options                    --mode clausify
% 2.88/0.99  --stdin                                 false
% 2.88/0.99  --stats_out                             all
% 2.88/0.99  
% 2.88/0.99  ------ General Options
% 2.88/0.99  
% 2.88/0.99  --fof                                   false
% 2.88/0.99  --time_out_real                         305.
% 2.88/0.99  --time_out_virtual                      -1.
% 2.88/0.99  --symbol_type_check                     false
% 2.88/0.99  --clausify_out                          false
% 2.88/0.99  --sig_cnt_out                           false
% 2.88/0.99  --trig_cnt_out                          false
% 2.88/0.99  --trig_cnt_out_tolerance                1.
% 2.88/0.99  --trig_cnt_out_sk_spl                   false
% 2.88/0.99  --abstr_cl_out                          false
% 2.88/0.99  
% 2.88/0.99  ------ Global Options
% 2.88/0.99  
% 2.88/0.99  --schedule                              default
% 2.88/0.99  --add_important_lit                     false
% 2.88/0.99  --prop_solver_per_cl                    1000
% 2.88/0.99  --min_unsat_core                        false
% 2.88/0.99  --soft_assumptions                      false
% 2.88/0.99  --soft_lemma_size                       3
% 2.88/0.99  --prop_impl_unit_size                   0
% 2.88/0.99  --prop_impl_unit                        []
% 2.88/0.99  --share_sel_clauses                     true
% 2.88/0.99  --reset_solvers                         false
% 2.88/0.99  --bc_imp_inh                            [conj_cone]
% 2.88/0.99  --conj_cone_tolerance                   3.
% 2.88/0.99  --extra_neg_conj                        none
% 2.88/0.99  --large_theory_mode                     true
% 2.88/0.99  --prolific_symb_bound                   200
% 2.88/0.99  --lt_threshold                          2000
% 2.88/0.99  --clause_weak_htbl                      true
% 2.88/0.99  --gc_record_bc_elim                     false
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing Options
% 2.88/0.99  
% 2.88/0.99  --preprocessing_flag                    true
% 2.88/0.99  --time_out_prep_mult                    0.1
% 2.88/0.99  --splitting_mode                        input
% 2.88/0.99  --splitting_grd                         true
% 2.88/0.99  --splitting_cvd                         false
% 2.88/0.99  --splitting_cvd_svl                     false
% 2.88/0.99  --splitting_nvd                         32
% 2.88/0.99  --sub_typing                            true
% 2.88/0.99  --prep_gs_sim                           true
% 2.88/0.99  --prep_unflatten                        true
% 2.88/0.99  --prep_res_sim                          true
% 2.88/0.99  --prep_upred                            true
% 2.88/0.99  --prep_sem_filter                       exhaustive
% 2.88/0.99  --prep_sem_filter_out                   false
% 2.88/0.99  --pred_elim                             true
% 2.88/0.99  --res_sim_input                         true
% 2.88/0.99  --eq_ax_congr_red                       true
% 2.88/0.99  --pure_diseq_elim                       true
% 2.88/0.99  --brand_transform                       false
% 2.88/0.99  --non_eq_to_eq                          false
% 2.88/0.99  --prep_def_merge                        true
% 2.88/0.99  --prep_def_merge_prop_impl              false
% 2.88/0.99  --prep_def_merge_mbd                    true
% 2.88/0.99  --prep_def_merge_tr_red                 false
% 2.88/0.99  --prep_def_merge_tr_cl                  false
% 2.88/0.99  --smt_preprocessing                     true
% 2.88/0.99  --smt_ac_axioms                         fast
% 2.88/0.99  --preprocessed_out                      false
% 2.88/0.99  --preprocessed_stats                    false
% 2.88/0.99  
% 2.88/0.99  ------ Abstraction refinement Options
% 2.88/0.99  
% 2.88/0.99  --abstr_ref                             []
% 2.88/0.99  --abstr_ref_prep                        false
% 2.88/0.99  --abstr_ref_until_sat                   false
% 2.88/0.99  --abstr_ref_sig_restrict                funpre
% 2.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/0.99  --abstr_ref_under                       []
% 2.88/0.99  
% 2.88/0.99  ------ SAT Options
% 2.88/0.99  
% 2.88/0.99  --sat_mode                              false
% 2.88/0.99  --sat_fm_restart_options                ""
% 2.88/0.99  --sat_gr_def                            false
% 2.88/0.99  --sat_epr_types                         true
% 2.88/0.99  --sat_non_cyclic_types                  false
% 2.88/0.99  --sat_finite_models                     false
% 2.88/0.99  --sat_fm_lemmas                         false
% 2.88/0.99  --sat_fm_prep                           false
% 2.88/0.99  --sat_fm_uc_incr                        true
% 2.88/0.99  --sat_out_model                         small
% 2.88/0.99  --sat_out_clauses                       false
% 2.88/0.99  
% 2.88/0.99  ------ QBF Options
% 2.88/0.99  
% 2.88/0.99  --qbf_mode                              false
% 2.88/0.99  --qbf_elim_univ                         false
% 2.88/0.99  --qbf_dom_inst                          none
% 2.88/0.99  --qbf_dom_pre_inst                      false
% 2.88/0.99  --qbf_sk_in                             false
% 2.88/0.99  --qbf_pred_elim                         true
% 2.88/0.99  --qbf_split                             512
% 2.88/0.99  
% 2.88/0.99  ------ BMC1 Options
% 2.88/0.99  
% 2.88/0.99  --bmc1_incremental                      false
% 2.88/0.99  --bmc1_axioms                           reachable_all
% 2.88/0.99  --bmc1_min_bound                        0
% 2.88/0.99  --bmc1_max_bound                        -1
% 2.88/0.99  --bmc1_max_bound_default                -1
% 2.88/0.99  --bmc1_symbol_reachability              true
% 2.88/0.99  --bmc1_property_lemmas                  false
% 2.88/0.99  --bmc1_k_induction                      false
% 2.88/0.99  --bmc1_non_equiv_states                 false
% 2.88/0.99  --bmc1_deadlock                         false
% 2.88/0.99  --bmc1_ucm                              false
% 2.88/0.99  --bmc1_add_unsat_core                   none
% 2.88/0.99  --bmc1_unsat_core_children              false
% 2.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/0.99  --bmc1_out_stat                         full
% 2.88/0.99  --bmc1_ground_init                      false
% 2.88/0.99  --bmc1_pre_inst_next_state              false
% 2.88/0.99  --bmc1_pre_inst_state                   false
% 2.88/0.99  --bmc1_pre_inst_reach_state             false
% 2.88/0.99  --bmc1_out_unsat_core                   false
% 2.88/0.99  --bmc1_aig_witness_out                  false
% 2.88/0.99  --bmc1_verbose                          false
% 2.88/0.99  --bmc1_dump_clauses_tptp                false
% 2.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.88/0.99  --bmc1_dump_file                        -
% 2.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.88/0.99  --bmc1_ucm_extend_mode                  1
% 2.88/0.99  --bmc1_ucm_init_mode                    2
% 2.88/0.99  --bmc1_ucm_cone_mode                    none
% 2.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.88/0.99  --bmc1_ucm_relax_model                  4
% 2.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/0.99  --bmc1_ucm_layered_model                none
% 2.88/0.99  --bmc1_ucm_max_lemma_size               10
% 2.88/0.99  
% 2.88/0.99  ------ AIG Options
% 2.88/0.99  
% 2.88/0.99  --aig_mode                              false
% 2.88/0.99  
% 2.88/0.99  ------ Instantiation Options
% 2.88/0.99  
% 2.88/0.99  --instantiation_flag                    true
% 2.88/0.99  --inst_sos_flag                         false
% 2.88/0.99  --inst_sos_phase                        true
% 2.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel_side                     none
% 2.88/0.99  --inst_solver_per_active                1400
% 2.88/0.99  --inst_solver_calls_frac                1.
% 2.88/0.99  --inst_passive_queue_type               priority_queues
% 2.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/0.99  --inst_passive_queues_freq              [25;2]
% 2.88/0.99  --inst_dismatching                      true
% 2.88/0.99  --inst_eager_unprocessed_to_passive     true
% 2.88/0.99  --inst_prop_sim_given                   true
% 2.88/0.99  --inst_prop_sim_new                     false
% 2.88/0.99  --inst_subs_new                         false
% 2.88/0.99  --inst_eq_res_simp                      false
% 2.88/0.99  --inst_subs_given                       false
% 2.88/0.99  --inst_orphan_elimination               true
% 2.88/0.99  --inst_learning_loop_flag               true
% 2.88/0.99  --inst_learning_start                   3000
% 2.88/0.99  --inst_learning_factor                  2
% 2.88/0.99  --inst_start_prop_sim_after_learn       3
% 2.88/0.99  --inst_sel_renew                        solver
% 2.88/0.99  --inst_lit_activity_flag                true
% 2.88/0.99  --inst_restr_to_given                   false
% 2.88/0.99  --inst_activity_threshold               500
% 2.88/0.99  --inst_out_proof                        true
% 2.88/0.99  
% 2.88/0.99  ------ Resolution Options
% 2.88/0.99  
% 2.88/0.99  --resolution_flag                       false
% 2.88/0.99  --res_lit_sel                           adaptive
% 2.88/0.99  --res_lit_sel_side                      none
% 2.88/0.99  --res_ordering                          kbo
% 2.88/0.99  --res_to_prop_solver                    active
% 2.88/0.99  --res_prop_simpl_new                    false
% 2.88/0.99  --res_prop_simpl_given                  true
% 2.88/0.99  --res_passive_queue_type                priority_queues
% 2.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/0.99  --res_passive_queues_freq               [15;5]
% 2.88/0.99  --res_forward_subs                      full
% 2.88/0.99  --res_backward_subs                     full
% 2.88/0.99  --res_forward_subs_resolution           true
% 2.88/0.99  --res_backward_subs_resolution          true
% 2.88/0.99  --res_orphan_elimination                true
% 2.88/0.99  --res_time_limit                        2.
% 2.88/0.99  --res_out_proof                         true
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Options
% 2.88/0.99  
% 2.88/0.99  --superposition_flag                    true
% 2.88/0.99  --sup_passive_queue_type                priority_queues
% 2.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.88/0.99  --demod_completeness_check              fast
% 2.88/0.99  --demod_use_ground                      true
% 2.88/0.99  --sup_to_prop_solver                    passive
% 2.88/0.99  --sup_prop_simpl_new                    true
% 2.88/0.99  --sup_prop_simpl_given                  true
% 2.88/0.99  --sup_fun_splitting                     false
% 2.88/0.99  --sup_smt_interval                      50000
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Simplification Setup
% 2.88/0.99  
% 2.88/0.99  --sup_indices_passive                   []
% 2.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_full_bw                           [BwDemod]
% 2.88/0.99  --sup_immed_triv                        [TrivRules]
% 2.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_immed_bw_main                     []
% 2.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  
% 2.88/0.99  ------ Combination Options
% 2.88/0.99  
% 2.88/0.99  --comb_res_mult                         3
% 2.88/0.99  --comb_sup_mult                         2
% 2.88/0.99  --comb_inst_mult                        10
% 2.88/0.99  
% 2.88/0.99  ------ Debug Options
% 2.88/0.99  
% 2.88/0.99  --dbg_backtrace                         false
% 2.88/0.99  --dbg_dump_prop_clauses                 false
% 2.88/0.99  --dbg_dump_prop_clauses_file            -
% 2.88/0.99  --dbg_out_stat                          false
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  ------ Proving...
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  % SZS status Theorem for theBenchmark.p
% 2.88/0.99  
% 2.88/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.88/0.99  
% 2.88/0.99  fof(f4,conjecture,(
% 2.88/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f5,negated_conjecture,(
% 2.88/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.88/0.99    inference(negated_conjecture,[],[f4])).
% 2.88/0.99  
% 2.88/0.99  fof(f11,plain,(
% 2.88/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.88/0.99    inference(ennf_transformation,[],[f5])).
% 2.88/0.99  
% 2.88/0.99  fof(f12,plain,(
% 2.88/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.88/0.99    inference(flattening,[],[f11])).
% 2.88/0.99  
% 2.88/0.99  fof(f23,plain,(
% 2.88/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5))) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.88/0.99    inference(nnf_transformation,[],[f12])).
% 2.88/0.99  
% 2.88/0.99  fof(f24,plain,(
% 2.88/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.88/0.99    inference(flattening,[],[f23])).
% 2.88/0.99  
% 2.88/0.99  fof(f31,plain,(
% 2.88/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK9) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK9) | r1_tmap_1(X1,X0,X2,X5)) & sK9 = X5 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(sK9,u1_struct_0(X3)))) )),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f30,plain,(
% 2.88/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,sK8)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,sK8)) & sK8 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(sK8,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK8,u1_struct_0(X1)))) )),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f29,plain,(
% 2.88/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(sK7,u1_struct_0(X3)) & r2_hidden(X5,sK7) & v3_pre_topc(sK7,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f28,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK6,X0,k2_tmap_1(X1,X0,X2,sK6),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(sK6,X0,k2_tmap_1(X1,X0,X2,sK6),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(sK6)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(sK6))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK6,X1) & ~v2_struct_0(sK6))) )),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f27,plain,(
% 2.88/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK5,X3),X6) | ~r1_tmap_1(X1,X0,sK5,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK5,X3),X6) | r1_tmap_1(X1,X0,sK5,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f26,plain,(
% 2.88/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK4,X0,X2,X3),X6) | ~r1_tmap_1(sK4,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK4,X0,X2,X3),X6) | r1_tmap_1(sK4,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK4) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))) )),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f25,plain,(
% 2.88/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK3,k2_tmap_1(X1,sK3,X2,X3),X6) | ~r1_tmap_1(X1,sK3,X2,X5)) & (r1_tmap_1(X3,sK3,k2_tmap_1(X1,sK3,X2,X3),X6) | r1_tmap_1(X1,sK3,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f32,plain,(
% 2.88/0.99    (((((((~r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) | ~r1_tmap_1(sK4,sK3,sK5,sK8)) & (r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) | r1_tmap_1(sK4,sK3,sK5,sK8)) & sK8 = sK9 & r1_tarski(sK7,u1_struct_0(sK6)) & r2_hidden(sK8,sK7) & v3_pre_topc(sK7,sK4) & m1_subset_1(sK9,u1_struct_0(sK6))) & m1_subset_1(sK8,u1_struct_0(sK4))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_pre_topc(sK6,sK4) & ~v2_struct_0(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f24,f31,f30,f29,f28,f27,f26,f25])).
% 2.88/0.99  
% 2.88/0.99  fof(f55,plain,(
% 2.88/0.99    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f2,axiom,(
% 2.88/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f7,plain,(
% 2.88/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.88/0.99    inference(ennf_transformation,[],[f2])).
% 2.88/0.99  
% 2.88/0.99  fof(f8,plain,(
% 2.88/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.88/0.99    inference(flattening,[],[f7])).
% 2.88/0.99  
% 2.88/0.99  fof(f17,plain,(
% 2.88/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.88/0.99    inference(nnf_transformation,[],[f8])).
% 2.88/0.99  
% 2.88/0.99  fof(f18,plain,(
% 2.88/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.88/0.99    inference(rectify,[],[f17])).
% 2.88/0.99  
% 2.88/0.99  fof(f20,plain,(
% 2.88/0.99    ! [X4,X1,X0] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK2(X0,X1,X4),X1) & m1_connsp_2(sK2(X0,X1,X4),X0,X4) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f19,plain,(
% 2.88/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK1(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f21,plain,(
% 2.88/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK1(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X4] : ((r1_tarski(sK2(X0,X1,X4),X1) & m1_connsp_2(sK2(X0,X1,X4),X0,X4) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f20,f19])).
% 2.88/0.99  
% 2.88/0.99  fof(f37,plain,(
% 2.88/0.99    ( ! [X4,X0,X1] : (m1_connsp_2(sK2(X0,X1,X4),X0,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f21])).
% 2.88/0.99  
% 2.88/0.99  fof(f49,plain,(
% 2.88/0.99    l1_pre_topc(sK4)),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f47,plain,(
% 2.88/0.99    ~v2_struct_0(sK4)),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f48,plain,(
% 2.88/0.99    v2_pre_topc(sK4)),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f38,plain,(
% 2.88/0.99    ( ! [X4,X0,X1] : (r1_tarski(sK2(X0,X1,X4),X1) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f21])).
% 2.88/0.99  
% 2.88/0.99  fof(f1,axiom,(
% 2.88/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f6,plain,(
% 2.88/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.88/0.99    inference(ennf_transformation,[],[f1])).
% 2.88/0.99  
% 2.88/0.99  fof(f13,plain,(
% 2.88/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.88/0.99    inference(nnf_transformation,[],[f6])).
% 2.88/0.99  
% 2.88/0.99  fof(f14,plain,(
% 2.88/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.88/0.99    inference(rectify,[],[f13])).
% 2.88/0.99  
% 2.88/0.99  fof(f15,plain,(
% 2.88/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f16,plain,(
% 2.88/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 2.88/0.99  
% 2.88/0.99  fof(f34,plain,(
% 2.88/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f16])).
% 2.88/0.99  
% 2.88/0.99  fof(f33,plain,(
% 2.88/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f16])).
% 2.88/0.99  
% 2.88/0.99  fof(f35,plain,(
% 2.88/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f16])).
% 2.88/0.99  
% 2.88/0.99  fof(f36,plain,(
% 2.88/0.99    ( ! [X4,X0,X1] : (m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f21])).
% 2.88/0.99  
% 2.88/0.99  fof(f62,plain,(
% 2.88/0.99    r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) | r1_tmap_1(sK4,sK3,sK5,sK8)),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f61,plain,(
% 2.88/0.99    sK8 = sK9),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f51,plain,(
% 2.88/0.99    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f3,axiom,(
% 2.88/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f9,plain,(
% 2.88/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.88/0.99    inference(ennf_transformation,[],[f3])).
% 2.88/0.99  
% 2.88/0.99  fof(f10,plain,(
% 2.88/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.88/0.99    inference(flattening,[],[f9])).
% 2.88/0.99  
% 2.88/0.99  fof(f22,plain,(
% 2.88/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.88/0.99    inference(nnf_transformation,[],[f10])).
% 2.88/0.99  
% 2.88/0.99  fof(f43,plain,(
% 2.88/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f22])).
% 2.88/0.99  
% 2.88/0.99  fof(f64,plain,(
% 2.88/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.88/0.99    inference(equality_resolution,[],[f43])).
% 2.88/0.99  
% 2.88/0.99  fof(f54,plain,(
% 2.88/0.99    m1_pre_topc(sK6,sK4)),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f53,plain,(
% 2.88/0.99    ~v2_struct_0(sK6)),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f50,plain,(
% 2.88/0.99    v1_funct_1(sK5)),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f46,plain,(
% 2.88/0.99    l1_pre_topc(sK3)),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f44,plain,(
% 2.88/0.99    ~v2_struct_0(sK3)),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f45,plain,(
% 2.88/0.99    v2_pre_topc(sK3)),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f52,plain,(
% 2.88/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f57,plain,(
% 2.88/0.99    m1_subset_1(sK9,u1_struct_0(sK6))),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f63,plain,(
% 2.88/0.99    ~r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) | ~r1_tmap_1(sK4,sK3,sK5,sK8)),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f56,plain,(
% 2.88/0.99    m1_subset_1(sK8,u1_struct_0(sK4))),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f42,plain,(
% 2.88/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f22])).
% 2.88/0.99  
% 2.88/0.99  fof(f65,plain,(
% 2.88/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.88/0.99    inference(equality_resolution,[],[f42])).
% 2.88/0.99  
% 2.88/0.99  fof(f59,plain,(
% 2.88/0.99    r2_hidden(sK8,sK7)),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f60,plain,(
% 2.88/0.99    r1_tarski(sK7,u1_struct_0(sK6))),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f58,plain,(
% 2.88/0.99    v3_pre_topc(sK7,sK4)),
% 2.88/0.99    inference(cnf_transformation,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  cnf(c_19,negated_conjecture,
% 2.88/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.88/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7282,negated_conjecture,
% 2.88/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8052,plain,
% 2.88/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_7282]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7,plain,
% 2.88/0.99      ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.88/0.99      | ~ v3_pre_topc(X1,X0)
% 2.88/0.99      | ~ r2_hidden(X2,X1)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | ~ l1_pre_topc(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_25,negated_conjecture,
% 2.88/0.99      ( l1_pre_topc(sK4) ),
% 2.88/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_818,plain,
% 2.88/0.99      ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.88/0.99      | ~ v3_pre_topc(X1,X0)
% 2.88/0.99      | ~ r2_hidden(X2,X1)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | sK4 != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_25]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_819,plain,
% 2.88/0.99      ( m1_connsp_2(sK2(sK4,X0,X1),sK4,X1)
% 2.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | ~ v3_pre_topc(X0,sK4)
% 2.88/0.99      | ~ r2_hidden(X1,X0)
% 2.88/0.99      | v2_struct_0(sK4)
% 2.88/0.99      | ~ v2_pre_topc(sK4) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_818]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_27,negated_conjecture,
% 2.88/0.99      ( ~ v2_struct_0(sK4) ),
% 2.88/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_26,negated_conjecture,
% 2.88/0.99      ( v2_pre_topc(sK4) ),
% 2.88/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_823,plain,
% 2.88/0.99      ( m1_connsp_2(sK2(sK4,X0,X1),sK4,X1)
% 2.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | ~ v3_pre_topc(X0,sK4)
% 2.88/0.99      | ~ r2_hidden(X1,X0) ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_819,c_27,c_26]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7278,plain,
% 2.88/0.99      ( m1_connsp_2(sK2(sK4,X0_55,X1_55),sK4,X1_55)
% 2.88/0.99      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK4))
% 2.88/0.99      | ~ v3_pre_topc(X0_55,sK4)
% 2.88/0.99      | ~ r2_hidden(X1_55,X0_55) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_823]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8058,plain,
% 2.88/0.99      ( m1_connsp_2(sK2(sK4,X0_55,X1_55),sK4,X1_55) = iProver_top
% 2.88/0.99      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.88/0.99      | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | v3_pre_topc(X0_55,sK4) != iProver_top
% 2.88/0.99      | r2_hidden(X1_55,X0_55) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_7278]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_6,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.88/0.99      | ~ v3_pre_topc(X0,X1)
% 2.88/0.99      | ~ r2_hidden(X2,X0)
% 2.88/0.99      | r1_tarski(sK2(X1,X0,X2),X0)
% 2.88/0.99      | v2_struct_0(X1)
% 2.88/0.99      | ~ v2_pre_topc(X1)
% 2.88/0.99      | ~ l1_pre_topc(X1) ),
% 2.88/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_971,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.88/0.99      | ~ v3_pre_topc(X0,X1)
% 2.88/0.99      | ~ r2_hidden(X2,X0)
% 2.88/0.99      | r1_tarski(sK2(X1,X0,X2),X0)
% 2.88/0.99      | v2_struct_0(X1)
% 2.88/0.99      | ~ v2_pre_topc(X1)
% 2.88/0.99      | sK4 != X1 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_25]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_972,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | ~ v3_pre_topc(X0,sK4)
% 2.88/0.99      | ~ r2_hidden(X1,X0)
% 2.88/0.99      | r1_tarski(sK2(sK4,X0,X1),X0)
% 2.88/0.99      | v2_struct_0(sK4)
% 2.88/0.99      | ~ v2_pre_topc(sK4) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_971]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_976,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | ~ v3_pre_topc(X0,sK4)
% 2.88/0.99      | ~ r2_hidden(X1,X0)
% 2.88/0.99      | r1_tarski(sK2(sK4,X0,X1),X0) ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_972,c_27,c_26]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7275,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK4))
% 2.88/0.99      | ~ v3_pre_topc(X0_55,sK4)
% 2.88/0.99      | ~ r2_hidden(X1_55,X0_55)
% 2.88/0.99      | r1_tarski(sK2(sK4,X0_55,X1_55),X0_55) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_976]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8061,plain,
% 2.88/0.99      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.88/0.99      | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | v3_pre_topc(X0_55,sK4) != iProver_top
% 2.88/0.99      | r2_hidden(X1_55,X0_55) != iProver_top
% 2.88/0.99      | r1_tarski(sK2(sK4,X0_55,X1_55),X0_55) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_7275]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_1,plain,
% 2.88/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.88/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7292,plain,
% 2.88/0.99      ( r2_hidden(sK0(X0_55,X1_55),X0_55) | r1_tarski(X0_55,X1_55) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8043,plain,
% 2.88/0.99      ( r2_hidden(sK0(X0_55,X1_55),X0_55) = iProver_top
% 2.88/0.99      | r1_tarski(X0_55,X1_55) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_7292]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2,plain,
% 2.88/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.88/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7291,plain,
% 2.88/0.99      ( ~ r2_hidden(X0_55,X1_55)
% 2.88/0.99      | r2_hidden(X0_55,X2_55)
% 2.88/0.99      | ~ r1_tarski(X1_55,X2_55) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8044,plain,
% 2.88/0.99      ( r2_hidden(X0_55,X1_55) != iProver_top
% 2.88/0.99      | r2_hidden(X0_55,X2_55) = iProver_top
% 2.88/0.99      | r1_tarski(X1_55,X2_55) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_7291]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8564,plain,
% 2.88/0.99      ( r2_hidden(sK0(X0_55,X1_55),X2_55) = iProver_top
% 2.88/0.99      | r1_tarski(X0_55,X2_55) != iProver_top
% 2.88/0.99      | r1_tarski(X0_55,X1_55) = iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_8043,c_8044]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8914,plain,
% 2.88/0.99      ( r2_hidden(sK0(X0_55,X1_55),X2_55) = iProver_top
% 2.88/0.99      | r1_tarski(X0_55,X3_55) != iProver_top
% 2.88/0.99      | r1_tarski(X3_55,X2_55) != iProver_top
% 2.88/0.99      | r1_tarski(X0_55,X1_55) = iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_8564,c_8044]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8977,plain,
% 2.88/0.99      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.88/0.99      | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | v3_pre_topc(X0_55,sK4) != iProver_top
% 2.88/0.99      | r2_hidden(X1_55,X0_55) != iProver_top
% 2.88/0.99      | r2_hidden(sK0(sK2(sK4,X0_55,X1_55),X2_55),X3_55) = iProver_top
% 2.88/0.99      | r1_tarski(X0_55,X3_55) != iProver_top
% 2.88/0.99      | r1_tarski(sK2(sK4,X0_55,X1_55),X2_55) = iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_8061,c_8914]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_0,plain,
% 2.88/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.88/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7293,plain,
% 2.88/0.99      ( ~ r2_hidden(sK0(X0_55,X1_55),X1_55) | r1_tarski(X0_55,X1_55) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8042,plain,
% 2.88/0.99      ( r2_hidden(sK0(X0_55,X1_55),X1_55) != iProver_top
% 2.88/0.99      | r1_tarski(X0_55,X1_55) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_7293]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_10519,plain,
% 2.88/0.99      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.88/0.99      | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | v3_pre_topc(X0_55,sK4) != iProver_top
% 2.88/0.99      | r2_hidden(X1_55,X0_55) != iProver_top
% 2.88/0.99      | r1_tarski(X0_55,X2_55) != iProver_top
% 2.88/0.99      | r1_tarski(sK2(sK4,X0_55,X1_55),X2_55) = iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_8977,c_8042]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.88/0.99      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.99      | ~ v3_pre_topc(X0,X1)
% 2.88/0.99      | ~ r2_hidden(X2,X0)
% 2.88/0.99      | v2_struct_0(X1)
% 2.88/0.99      | ~ v2_pre_topc(X1)
% 2.88/0.99      | ~ l1_pre_topc(X1) ),
% 2.88/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_944,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.88/0.99      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.99      | ~ v3_pre_topc(X0,X1)
% 2.88/0.99      | ~ r2_hidden(X2,X0)
% 2.88/0.99      | v2_struct_0(X1)
% 2.88/0.99      | ~ v2_pre_topc(X1)
% 2.88/0.99      | sK4 != X1 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_945,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ v3_pre_topc(X0,sK4)
% 2.88/0.99      | ~ r2_hidden(X1,X0)
% 2.88/0.99      | v2_struct_0(sK4)
% 2.88/0.99      | ~ v2_pre_topc(sK4) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_944]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_949,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ v3_pre_topc(X0,sK4)
% 2.88/0.99      | ~ r2_hidden(X1,X0) ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_945,c_27,c_26]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7276,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK4))
% 2.88/0.99      | m1_subset_1(sK2(sK4,X0_55,X1_55),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ v3_pre_topc(X0_55,sK4)
% 2.88/0.99      | ~ r2_hidden(X1_55,X0_55) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_949]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8060,plain,
% 2.88/0.99      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.88/0.99      | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | m1_subset_1(sK2(sK4,X0_55,X1_55),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.88/0.99      | v3_pre_topc(X0_55,sK4) != iProver_top
% 2.88/0.99      | r2_hidden(X1_55,X0_55) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_7276]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_12,negated_conjecture,
% 2.88/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK8)
% 2.88/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) ),
% 2.88/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7289,negated_conjecture,
% 2.88/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK8)
% 2.88/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8046,plain,
% 2.88/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK8) = iProver_top
% 2.88/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_7289]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_13,negated_conjecture,
% 2.88/0.99      ( sK8 = sK9 ),
% 2.88/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7288,negated_conjecture,
% 2.88/0.99      ( sK8 = sK9 ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8104,plain,
% 2.88/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK9) = iProver_top
% 2.88/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) = iProver_top ),
% 2.88/0.99      inference(light_normalisation,[status(thm)],[c_8046,c_7288]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_23,negated_conjecture,
% 2.88/0.99      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 2.88/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_9,plain,
% 2.88/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.88/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.88/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.88/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.88/0.99      | ~ m1_pre_topc(X4,X0)
% 2.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.88/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.88/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.88/0.99      | ~ v1_funct_1(X2)
% 2.88/0.99      | v2_struct_0(X1)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | v2_struct_0(X4)
% 2.88/0.99      | ~ v2_pre_topc(X1)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | ~ l1_pre_topc(X1)
% 2.88/0.99      | ~ l1_pre_topc(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_20,negated_conjecture,
% 2.88/0.99      ( m1_pre_topc(sK6,sK4) ),
% 2.88/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_437,plain,
% 2.88/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.88/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.88/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.88/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.88/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.88/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.88/0.99      | ~ v1_funct_1(X2)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | v2_struct_0(X1)
% 2.88/0.99      | v2_struct_0(X4)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | ~ v2_pre_topc(X1)
% 2.88/0.99      | ~ l1_pre_topc(X0)
% 2.88/0.99      | ~ l1_pre_topc(X1)
% 2.88/0.99      | sK4 != X0
% 2.88/0.99      | sK6 != X4 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_438,plain,
% 2.88/0.99      ( r1_tmap_1(sK4,X0,X1,X2)
% 2.88/0.99      | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
% 2.88/0.99      | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
% 2.88/0.99      | ~ m1_connsp_2(X3,sK4,X2)
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.88/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 2.88/0.99      | ~ r1_tarski(X3,u1_struct_0(sK6))
% 2.88/0.99      | ~ v1_funct_1(X1)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | v2_struct_0(sK4)
% 2.88/0.99      | v2_struct_0(sK6)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | ~ v2_pre_topc(sK4)
% 2.88/0.99      | ~ l1_pre_topc(X0)
% 2.88/0.99      | ~ l1_pre_topc(sK4) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_437]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_21,negated_conjecture,
% 2.88/0.99      ( ~ v2_struct_0(sK6) ),
% 2.88/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_442,plain,
% 2.88/0.99      ( ~ l1_pre_topc(X0)
% 2.88/0.99      | r1_tmap_1(sK4,X0,X1,X2)
% 2.88/0.99      | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
% 2.88/0.99      | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
% 2.88/0.99      | ~ m1_connsp_2(X3,sK4,X2)
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.88/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 2.88/0.99      | ~ r1_tarski(X3,u1_struct_0(sK6))
% 2.88/0.99      | ~ v1_funct_1(X1)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | ~ v2_pre_topc(X0) ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_438,c_27,c_26,c_25,c_21]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_443,plain,
% 2.88/0.99      ( r1_tmap_1(sK4,X0,X1,X2)
% 2.88/0.99      | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
% 2.88/0.99      | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
% 2.88/0.99      | ~ m1_connsp_2(X3,sK4,X2)
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.88/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 2.88/0.99      | ~ r1_tarski(X3,u1_struct_0(sK6))
% 2.88/0.99      | ~ v1_funct_1(X1)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | ~ l1_pre_topc(X0) ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_442]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_490,plain,
% 2.88/0.99      ( r1_tmap_1(sK4,X0,X1,X2)
% 2.88/0.99      | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
% 2.88/0.99      | ~ m1_connsp_2(X3,sK4,X2)
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.88/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 2.88/0.99      | ~ r1_tarski(X3,u1_struct_0(sK6))
% 2.88/0.99      | ~ v1_funct_1(X1)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | ~ l1_pre_topc(X0)
% 2.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.88/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.88/0.99      | sK5 != X1 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_443]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_491,plain,
% 2.88/0.99      ( r1_tmap_1(sK4,X0,sK5,X1)
% 2.88/0.99      | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 2.88/0.99      | ~ m1_connsp_2(X2,sK4,X1)
% 2.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.88/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.88/0.99      | ~ r1_tarski(X2,u1_struct_0(sK6))
% 2.88/0.99      | ~ v1_funct_1(sK5)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | ~ l1_pre_topc(X0)
% 2.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_490]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_24,negated_conjecture,
% 2.88/0.99      ( v1_funct_1(sK5) ),
% 2.88/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_495,plain,
% 2.88/0.99      ( ~ r1_tarski(X2,u1_struct_0(sK6))
% 2.88/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_connsp_2(X2,sK4,X1)
% 2.88/0.99      | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 2.88/0.99      | r1_tmap_1(sK4,X0,sK5,X1)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | ~ l1_pre_topc(X0)
% 2.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_491,c_24]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_496,plain,
% 2.88/0.99      ( r1_tmap_1(sK4,X0,sK5,X1)
% 2.88/0.99      | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 2.88/0.99      | ~ m1_connsp_2(X2,sK4,X1)
% 2.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.88/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.88/0.99      | ~ r1_tarski(X2,u1_struct_0(sK6))
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | ~ l1_pre_topc(X0)
% 2.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_495]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_28,negated_conjecture,
% 2.88/0.99      ( l1_pre_topc(sK3) ),
% 2.88/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_881,plain,
% 2.88/0.99      ( r1_tmap_1(sK4,X0,sK5,X1)
% 2.88/0.99      | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 2.88/0.99      | ~ m1_connsp_2(X2,sK4,X1)
% 2.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.88/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.88/0.99      | ~ r1_tarski(X2,u1_struct_0(sK6))
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.88/0.99      | sK3 != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_496,c_28]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_882,plain,
% 2.88/0.99      ( r1_tmap_1(sK4,sK3,sK5,X0)
% 2.88/0.99      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 2.88/0.99      | ~ m1_connsp_2(X1,sK4,X0)
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.88/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 2.88/0.99      | ~ r1_tarski(X1,u1_struct_0(sK6))
% 2.88/0.99      | v2_struct_0(sK3)
% 2.88/0.99      | ~ v2_pre_topc(sK3)
% 2.88/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_881]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_30,negated_conjecture,
% 2.88/0.99      ( ~ v2_struct_0(sK3) ),
% 2.88/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_29,negated_conjecture,
% 2.88/0.99      ( v2_pre_topc(sK3) ),
% 2.88/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_22,negated_conjecture,
% 2.88/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 2.88/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_886,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_connsp_2(X1,sK4,X0)
% 2.88/0.99      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 2.88/0.99      | r1_tmap_1(sK4,sK3,sK5,X0)
% 2.88/0.99      | ~ r1_tarski(X1,u1_struct_0(sK6))
% 2.88/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_882,c_30,c_29,c_22]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_887,plain,
% 2.88/0.99      ( r1_tmap_1(sK4,sK3,sK5,X0)
% 2.88/0.99      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 2.88/0.99      | ~ m1_connsp_2(X1,sK4,X0)
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.88/0.99      | ~ r1_tarski(X1,u1_struct_0(sK6))
% 2.88/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_886]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4279,plain,
% 2.88/0.99      ( r1_tmap_1(sK4,sK3,sK5,X0)
% 2.88/0.99      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 2.88/0.99      | ~ m1_connsp_2(X1,sK4,X0)
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.88/0.99      | ~ r1_tarski(X1,u1_struct_0(sK6)) ),
% 2.88/0.99      inference(equality_resolution_simp,[status(thm)],[c_887]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7266,plain,
% 2.88/0.99      ( r1_tmap_1(sK4,sK3,sK5,X0_55)
% 2.88/0.99      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55)
% 2.88/0.99      | ~ m1_connsp_2(X1_55,sK4,X0_55)
% 2.88/0.99      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
% 2.88/0.99      | ~ r1_tarski(X1_55,u1_struct_0(sK6)) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_4279]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8070,plain,
% 2.88/0.99      ( r1_tmap_1(sK4,sK3,sK5,X0_55) = iProver_top
% 2.88/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55) != iProver_top
% 2.88/0.99      | m1_connsp_2(X1_55,sK4,X0_55) != iProver_top
% 2.88/0.99      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.88/0.99      | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top
% 2.88/0.99      | r1_tarski(X1_55,u1_struct_0(sK6)) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_7266]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_9634,plain,
% 2.88/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK9) = iProver_top
% 2.88/0.99      | m1_connsp_2(X0_55,sK4,sK9) != iProver_top
% 2.88/0.99      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.88/0.99      | m1_subset_1(sK9,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
% 2.88/0.99      | r1_tarski(X0_55,u1_struct_0(sK6)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_8104,c_8070]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_17,negated_conjecture,
% 2.88/0.99      ( m1_subset_1(sK9,u1_struct_0(sK6)) ),
% 2.88/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_44,plain,
% 2.88/0.99      ( m1_subset_1(sK9,u1_struct_0(sK6)) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_11,negated_conjecture,
% 2.88/0.99      ( ~ r1_tmap_1(sK4,sK3,sK5,sK8)
% 2.88/0.99      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) ),
% 2.88/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7290,negated_conjecture,
% 2.88/0.99      ( ~ r1_tmap_1(sK4,sK3,sK5,sK8)
% 2.88/0.99      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8045,plain,
% 2.88/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK8) != iProver_top
% 2.88/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_7290]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8109,plain,
% 2.88/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK9) != iProver_top
% 2.88/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) != iProver_top ),
% 2.88/0.99      inference(light_normalisation,[status(thm)],[c_8045,c_7288]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_18,negated_conjecture,
% 2.88/0.99      ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
% 2.88/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7283,negated_conjecture,
% 2.88/0.99      ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8051,plain,
% 2.88/0.99      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_7283]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8083,plain,
% 2.88/0.99      ( m1_subset_1(sK9,u1_struct_0(sK4)) = iProver_top ),
% 2.88/0.99      inference(light_normalisation,[status(thm)],[c_8051,c_7288]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_10,plain,
% 2.88/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.88/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.88/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.88/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.88/0.99      | ~ m1_pre_topc(X4,X0)
% 2.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.88/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.88/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.88/0.99      | ~ v1_funct_1(X2)
% 2.88/0.99      | v2_struct_0(X1)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | v2_struct_0(X4)
% 2.88/0.99      | ~ v2_pre_topc(X1)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | ~ l1_pre_topc(X1)
% 2.88/0.99      | ~ l1_pre_topc(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_386,plain,
% 2.88/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.88/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.88/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.88/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.88/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.88/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.88/0.99      | ~ v1_funct_1(X2)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | v2_struct_0(X1)
% 2.88/0.99      | v2_struct_0(X4)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | ~ v2_pre_topc(X1)
% 2.88/0.99      | ~ l1_pre_topc(X0)
% 2.88/0.99      | ~ l1_pre_topc(X1)
% 2.88/0.99      | sK4 != X0
% 2.88/0.99      | sK6 != X4 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_387,plain,
% 2.88/0.99      ( ~ r1_tmap_1(sK4,X0,X1,X2)
% 2.88/0.99      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
% 2.88/0.99      | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
% 2.88/0.99      | ~ m1_connsp_2(X3,sK4,X2)
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.88/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 2.88/0.99      | ~ r1_tarski(X3,u1_struct_0(sK6))
% 2.88/0.99      | ~ v1_funct_1(X1)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | v2_struct_0(sK4)
% 2.88/0.99      | v2_struct_0(sK6)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | ~ v2_pre_topc(sK4)
% 2.88/0.99      | ~ l1_pre_topc(X0)
% 2.88/0.99      | ~ l1_pre_topc(sK4) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_386]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_391,plain,
% 2.88/0.99      ( ~ l1_pre_topc(X0)
% 2.88/0.99      | ~ r1_tmap_1(sK4,X0,X1,X2)
% 2.88/0.99      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
% 2.88/0.99      | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
% 2.88/0.99      | ~ m1_connsp_2(X3,sK4,X2)
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.88/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 2.88/0.99      | ~ r1_tarski(X3,u1_struct_0(sK6))
% 2.88/0.99      | ~ v1_funct_1(X1)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | ~ v2_pre_topc(X0) ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_387,c_27,c_26,c_25,c_21]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_392,plain,
% 2.88/0.99      ( ~ r1_tmap_1(sK4,X0,X1,X2)
% 2.88/0.99      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
% 2.88/0.99      | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
% 2.88/0.99      | ~ m1_connsp_2(X3,sK4,X2)
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.88/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 2.88/0.99      | ~ r1_tarski(X3,u1_struct_0(sK6))
% 2.88/0.99      | ~ v1_funct_1(X1)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | ~ l1_pre_topc(X0) ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_391]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_538,plain,
% 2.88/0.99      ( ~ r1_tmap_1(sK4,X0,X1,X2)
% 2.88/0.99      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
% 2.88/0.99      | ~ m1_connsp_2(X3,sK4,X2)
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.88/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 2.88/0.99      | ~ r1_tarski(X3,u1_struct_0(sK6))
% 2.88/0.99      | ~ v1_funct_1(X1)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | ~ l1_pre_topc(X0)
% 2.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.88/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.88/0.99      | sK5 != X1 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_392]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_539,plain,
% 2.88/0.99      ( ~ r1_tmap_1(sK4,X0,sK5,X1)
% 2.88/0.99      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 2.88/0.99      | ~ m1_connsp_2(X2,sK4,X1)
% 2.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.88/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.88/0.99      | ~ r1_tarski(X2,u1_struct_0(sK6))
% 2.88/0.99      | ~ v1_funct_1(sK5)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | ~ l1_pre_topc(X0)
% 2.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_538]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_543,plain,
% 2.88/0.99      ( ~ r1_tarski(X2,u1_struct_0(sK6))
% 2.88/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_connsp_2(X2,sK4,X1)
% 2.88/0.99      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 2.88/0.99      | ~ r1_tmap_1(sK4,X0,sK5,X1)
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | ~ l1_pre_topc(X0)
% 2.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_539,c_24]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_544,plain,
% 2.88/0.99      ( ~ r1_tmap_1(sK4,X0,sK5,X1)
% 2.88/0.99      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 2.88/0.99      | ~ m1_connsp_2(X2,sK4,X1)
% 2.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.88/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.88/0.99      | ~ r1_tarski(X2,u1_struct_0(sK6))
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | ~ l1_pre_topc(X0)
% 2.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_543]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_845,plain,
% 2.88/0.99      ( ~ r1_tmap_1(sK4,X0,sK5,X1)
% 2.88/0.99      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 2.88/0.99      | ~ m1_connsp_2(X2,sK4,X1)
% 2.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.88/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.88/0.99      | ~ r1_tarski(X2,u1_struct_0(sK6))
% 2.88/0.99      | v2_struct_0(X0)
% 2.88/0.99      | ~ v2_pre_topc(X0)
% 2.88/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.88/0.99      | sK3 != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_544,c_28]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_846,plain,
% 2.88/0.99      ( ~ r1_tmap_1(sK4,sK3,sK5,X0)
% 2.88/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 2.88/0.99      | ~ m1_connsp_2(X1,sK4,X0)
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.88/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 2.88/0.99      | ~ r1_tarski(X1,u1_struct_0(sK6))
% 2.88/0.99      | v2_struct_0(sK3)
% 2.88/0.99      | ~ v2_pre_topc(sK3)
% 2.88/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_845]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_850,plain,
% 2.88/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_connsp_2(X1,sK4,X0)
% 2.88/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 2.88/0.99      | ~ r1_tmap_1(sK4,sK3,sK5,X0)
% 2.88/0.99      | ~ r1_tarski(X1,u1_struct_0(sK6))
% 2.88/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_846,c_30,c_29,c_22]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_851,plain,
% 2.88/0.99      ( ~ r1_tmap_1(sK4,sK3,sK5,X0)
% 2.88/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 2.88/0.99      | ~ m1_connsp_2(X1,sK4,X0)
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.88/0.99      | ~ r1_tarski(X1,u1_struct_0(sK6))
% 2.88/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_850]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4283,plain,
% 2.88/0.99      ( ~ r1_tmap_1(sK4,sK3,sK5,X0)
% 2.88/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 2.88/0.99      | ~ m1_connsp_2(X1,sK4,X0)
% 2.88/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.88/0.99      | ~ r1_tarski(X1,u1_struct_0(sK6)) ),
% 2.88/0.99      inference(equality_resolution_simp,[status(thm)],[c_851]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7265,plain,
% 2.88/0.99      ( ~ r1_tmap_1(sK4,sK3,sK5,X0_55)
% 2.88/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55)
% 2.88/0.99      | ~ m1_connsp_2(X1_55,sK4,X0_55)
% 2.88/0.99      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
% 2.88/0.99      | ~ r1_tarski(X1_55,u1_struct_0(sK6)) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_4283]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_9652,plain,
% 2.88/0.99      ( ~ r1_tmap_1(sK4,sK3,sK5,sK9)
% 2.88/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9)
% 2.88/0.99      | ~ m1_connsp_2(X0_55,sK4,sK9)
% 2.88/0.99      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.88/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK6))
% 2.88/0.99      | ~ r1_tarski(X0_55,u1_struct_0(sK6)) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_7265]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_9653,plain,
% 2.88/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK9) != iProver_top
% 2.88/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK9) = iProver_top
% 2.88/0.99      | m1_connsp_2(X0_55,sK4,sK9) != iProver_top
% 2.88/0.99      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.88/0.99      | m1_subset_1(sK9,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
% 2.88/0.99      | r1_tarski(X0_55,u1_struct_0(sK6)) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_9652]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_9712,plain,
% 2.88/0.99      ( m1_connsp_2(X0_55,sK4,sK9) != iProver_top
% 2.88/0.99      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.88/0.99      | r1_tarski(X0_55,u1_struct_0(sK6)) != iProver_top ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_9634,c_44,c_8109,c_8083,c_9653]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_9722,plain,
% 2.88/0.99      ( m1_connsp_2(sK2(sK4,X0_55,X1_55),sK4,sK9) != iProver_top
% 2.88/0.99      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.88/0.99      | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | v3_pre_topc(X0_55,sK4) != iProver_top
% 2.88/0.99      | r2_hidden(X1_55,X0_55) != iProver_top
% 2.88/0.99      | r1_tarski(sK2(sK4,X0_55,X1_55),u1_struct_0(sK6)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_8060,c_9712]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_10613,plain,
% 2.88/0.99      ( m1_connsp_2(sK2(sK4,X0_55,X1_55),sK4,sK9) != iProver_top
% 2.88/0.99      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.88/0.99      | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | v3_pre_topc(X0_55,sK4) != iProver_top
% 2.88/0.99      | r2_hidden(X1_55,X0_55) != iProver_top
% 2.88/0.99      | r1_tarski(X0_55,u1_struct_0(sK6)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_10519,c_9722]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_11898,plain,
% 2.88/0.99      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.88/0.99      | m1_subset_1(sK9,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | v3_pre_topc(X0_55,sK4) != iProver_top
% 2.88/0.99      | r2_hidden(sK9,X0_55) != iProver_top
% 2.88/0.99      | r1_tarski(X0_55,u1_struct_0(sK6)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_8058,c_10613]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_11903,plain,
% 2.88/0.99      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.88/0.99      | v3_pre_topc(X0_55,sK4) != iProver_top
% 2.88/0.99      | r2_hidden(sK9,X0_55) != iProver_top
% 2.88/0.99      | r1_tarski(X0_55,u1_struct_0(sK6)) != iProver_top ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_11898,c_8083]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_11913,plain,
% 2.88/0.99      ( v3_pre_topc(sK7,sK4) != iProver_top
% 2.88/0.99      | r2_hidden(sK9,sK7) != iProver_top
% 2.88/0.99      | r1_tarski(sK7,u1_struct_0(sK6)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_8052,c_11903]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_15,negated_conjecture,
% 2.88/0.99      ( r2_hidden(sK8,sK7) ),
% 2.88/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7286,negated_conjecture,
% 2.88/0.99      ( r2_hidden(sK8,sK7) ),
% 2.88/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8048,plain,
% 2.88/0.99      ( r2_hidden(sK8,sK7) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_7286]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8074,plain,
% 2.88/0.99      ( r2_hidden(sK9,sK7) = iProver_top ),
% 2.88/0.99      inference(light_normalisation,[status(thm)],[c_8048,c_7288]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_14,negated_conjecture,
% 2.88/0.99      ( r1_tarski(sK7,u1_struct_0(sK6)) ),
% 2.88/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_47,plain,
% 2.88/0.99      ( r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_16,negated_conjecture,
% 2.88/0.99      ( v3_pre_topc(sK7,sK4) ),
% 2.88/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_45,plain,
% 2.88/0.99      ( v3_pre_topc(sK7,sK4) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(contradiction,plain,
% 2.88/0.99      ( $false ),
% 2.88/0.99      inference(minisat,[status(thm)],[c_11913,c_8074,c_47,c_45]) ).
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.88/0.99  
% 2.88/0.99  ------                               Statistics
% 2.88/0.99  
% 2.88/0.99  ------ General
% 2.88/0.99  
% 2.88/0.99  abstr_ref_over_cycles:                  0
% 2.88/0.99  abstr_ref_under_cycles:                 0
% 2.88/0.99  gc_basic_clause_elim:                   0
% 2.88/0.99  forced_gc_time:                         0
% 2.88/0.99  parsing_time:                           0.008
% 2.88/0.99  unif_index_cands_time:                  0.
% 2.88/0.99  unif_index_add_time:                    0.
% 2.88/0.99  orderings_time:                         0.
% 2.88/0.99  out_proof_time:                         0.013
% 2.88/0.99  total_time:                             0.293
% 2.88/0.99  num_of_symbols:                         61
% 2.88/0.99  num_of_terms:                           4757
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing
% 2.88/0.99  
% 2.88/0.99  num_of_splits:                          2
% 2.88/0.99  num_of_split_atoms:                     2
% 2.88/0.99  num_of_reused_defs:                     0
% 2.88/0.99  num_eq_ax_congr_red:                    28
% 2.88/0.99  num_of_sem_filtered_clauses:            1
% 2.88/0.99  num_of_subtypes:                        2
% 2.88/0.99  monotx_restored_types:                  0
% 2.88/0.99  sat_num_of_epr_types:                   0
% 2.88/0.99  sat_num_of_non_cyclic_types:            0
% 2.88/0.99  sat_guarded_non_collapsed_types:        0
% 2.88/0.99  num_pure_diseq_elim:                    0
% 2.88/0.99  simp_replaced_by:                       0
% 2.88/0.99  res_preprocessed:                       145
% 2.88/0.99  prep_upred:                             0
% 2.88/0.99  prep_unflattend:                        255
% 2.88/0.99  smt_new_axioms:                         0
% 2.88/0.99  pred_elim_cands:                        6
% 2.88/0.99  pred_elim:                              6
% 2.88/0.99  pred_elim_cl:                           2
% 2.88/0.99  pred_elim_cycles:                       13
% 2.88/0.99  merged_defs:                            8
% 2.88/0.99  merged_defs_ncl:                        0
% 2.88/0.99  bin_hyper_res:                          8
% 2.88/0.99  prep_cycles:                            4
% 2.88/0.99  pred_elim_time:                         0.131
% 2.88/0.99  splitting_time:                         0.
% 2.88/0.99  sem_filter_time:                        0.
% 2.88/0.99  monotx_time:                            0.
% 2.88/0.99  subtype_inf_time:                       0.
% 2.88/0.99  
% 2.88/0.99  ------ Problem properties
% 2.88/0.99  
% 2.88/0.99  clauses:                                31
% 2.88/0.99  conjectures:                            10
% 2.88/0.99  epr:                                    4
% 2.88/0.99  horn:                                   25
% 2.88/0.99  ground:                                 12
% 2.88/0.99  unary:                                  8
% 2.88/0.99  binary:                                 4
% 2.88/0.99  lits:                                   107
% 2.88/0.99  lits_eq:                                3
% 2.88/0.99  fd_pure:                                0
% 2.88/0.99  fd_pseudo:                              0
% 2.88/0.99  fd_cond:                                0
% 2.88/0.99  fd_pseudo_cond:                         0
% 2.88/0.99  ac_symbols:                             0
% 2.88/0.99  
% 2.88/0.99  ------ Propositional Solver
% 2.88/0.99  
% 2.88/0.99  prop_solver_calls:                      31
% 2.88/0.99  prop_fast_solver_calls:                 3308
% 2.88/0.99  smt_solver_calls:                       0
% 2.88/0.99  smt_fast_solver_calls:                  0
% 2.88/0.99  prop_num_of_clauses:                    1930
% 2.88/0.99  prop_preprocess_simplified:             6175
% 2.88/0.99  prop_fo_subsumed:                       90
% 2.88/0.99  prop_solver_time:                       0.
% 2.88/0.99  smt_solver_time:                        0.
% 2.88/0.99  smt_fast_solver_time:                   0.
% 2.88/0.99  prop_fast_solver_time:                  0.
% 2.88/0.99  prop_unsat_core_time:                   0.
% 2.88/0.99  
% 2.88/0.99  ------ QBF
% 2.88/0.99  
% 2.88/0.99  qbf_q_res:                              0
% 2.88/0.99  qbf_num_tautologies:                    0
% 2.88/0.99  qbf_prep_cycles:                        0
% 2.88/0.99  
% 2.88/0.99  ------ BMC1
% 2.88/0.99  
% 2.88/0.99  bmc1_current_bound:                     -1
% 2.88/0.99  bmc1_last_solved_bound:                 -1
% 2.88/0.99  bmc1_unsat_core_size:                   -1
% 2.88/0.99  bmc1_unsat_core_parents_size:           -1
% 2.88/0.99  bmc1_merge_next_fun:                    0
% 2.88/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.88/0.99  
% 2.88/0.99  ------ Instantiation
% 2.88/0.99  
% 2.88/0.99  inst_num_of_clauses:                    372
% 2.88/0.99  inst_num_in_passive:                    62
% 2.88/0.99  inst_num_in_active:                     303
% 2.88/0.99  inst_num_in_unprocessed:                7
% 2.88/0.99  inst_num_of_loops:                      400
% 2.88/0.99  inst_num_of_learning_restarts:          0
% 2.88/0.99  inst_num_moves_active_passive:          89
% 2.88/0.99  inst_lit_activity:                      0
% 2.88/0.99  inst_lit_activity_moves:                0
% 2.88/0.99  inst_num_tautologies:                   0
% 2.88/0.99  inst_num_prop_implied:                  0
% 2.88/0.99  inst_num_existing_simplified:           0
% 2.88/0.99  inst_num_eq_res_simplified:             0
% 2.88/0.99  inst_num_child_elim:                    0
% 2.88/0.99  inst_num_of_dismatching_blockings:      32
% 2.88/0.99  inst_num_of_non_proper_insts:           466
% 2.88/0.99  inst_num_of_duplicates:                 0
% 2.88/0.99  inst_inst_num_from_inst_to_res:         0
% 2.88/0.99  inst_dismatching_checking_time:         0.
% 2.88/0.99  
% 2.88/0.99  ------ Resolution
% 2.88/0.99  
% 2.88/0.99  res_num_of_clauses:                     0
% 2.88/0.99  res_num_in_passive:                     0
% 2.88/0.99  res_num_in_active:                      0
% 2.88/0.99  res_num_of_loops:                       149
% 2.88/0.99  res_forward_subset_subsumed:            91
% 2.88/0.99  res_backward_subset_subsumed:           2
% 2.88/0.99  res_forward_subsumed:                   0
% 2.88/0.99  res_backward_subsumed:                  0
% 2.88/0.99  res_forward_subsumption_resolution:     16
% 2.88/0.99  res_backward_subsumption_resolution:    0
% 2.88/0.99  res_clause_to_clause_subsumption:       1453
% 2.88/0.99  res_orphan_elimination:                 0
% 2.88/0.99  res_tautology_del:                      102
% 2.88/0.99  res_num_eq_res_simplified:              2
% 2.88/0.99  res_num_sel_changes:                    0
% 2.88/0.99  res_moves_from_active_to_pass:          0
% 2.88/0.99  
% 2.88/0.99  ------ Superposition
% 2.88/0.99  
% 2.88/0.99  sup_time_total:                         0.
% 2.88/0.99  sup_time_generating:                    0.
% 2.88/0.99  sup_time_sim_full:                      0.
% 2.88/0.99  sup_time_sim_immed:                     0.
% 2.88/0.99  
% 2.88/0.99  sup_num_of_clauses:                     110
% 2.88/0.99  sup_num_in_active:                      80
% 2.88/0.99  sup_num_in_passive:                     30
% 2.88/0.99  sup_num_of_loops:                       79
% 2.88/0.99  sup_fw_superposition:                   61
% 2.88/0.99  sup_bw_superposition:                   46
% 2.88/0.99  sup_immediate_simplified:               4
% 2.88/0.99  sup_given_eliminated:                   0
% 2.88/0.99  comparisons_done:                       0
% 2.88/0.99  comparisons_avoided:                    0
% 2.88/0.99  
% 2.88/0.99  ------ Simplifications
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  sim_fw_subset_subsumed:                 4
% 2.88/0.99  sim_bw_subset_subsumed:                 0
% 2.88/0.99  sim_fw_subsumed:                        0
% 2.88/0.99  sim_bw_subsumed:                        0
% 2.88/0.99  sim_fw_subsumption_res:                 3
% 2.88/0.99  sim_bw_subsumption_res:                 0
% 2.88/0.99  sim_tautology_del:                      6
% 2.88/0.99  sim_eq_tautology_del:                   0
% 2.88/0.99  sim_eq_res_simp:                        0
% 2.88/0.99  sim_fw_demodulated:                     0
% 2.88/0.99  sim_bw_demodulated:                     0
% 2.88/0.99  sim_light_normalised:                   4
% 2.88/0.99  sim_joinable_taut:                      0
% 2.88/0.99  sim_joinable_simp:                      0
% 2.88/0.99  sim_ac_normalised:                      0
% 2.88/0.99  sim_smt_subsumption:                    0
% 2.88/0.99  
%------------------------------------------------------------------------------
