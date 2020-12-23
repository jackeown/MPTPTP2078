%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:39 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 894 expanded)
%              Number of clauses        :  107 ( 141 expanded)
%              Number of leaves         :   18 ( 398 expanded)
%              Depth                    :   30
%              Number of atoms          : 1392 (17643 expanded)
%              Number of equality atoms :  127 (1110 expanded)
%              Maximal formula depth    :   27 (   9 average)
%              Maximal clause size      :   44 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,conjecture,(
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

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f34,plain,(
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
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8)
          | ~ r1_tmap_1(X1,X0,X2,X5) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8)
          | r1_tmap_1(X1,X0,X2,X5) )
        & sK8 = X5
        & r1_tarski(X4,u1_struct_0(X3))
        & r2_hidden(X5,X4)
        & v3_pre_topc(X4,X1)
        & m1_subset_1(sK8,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
              | ~ r1_tmap_1(X1,X0,X2,sK7) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
              | r1_tmap_1(X1,X0,X2,sK7) )
            & sK7 = X6
            & r1_tarski(X4,u1_struct_0(X3))
            & r2_hidden(sK7,X4)
            & v3_pre_topc(X4,X1)
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK7,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
                & r1_tarski(sK6,u1_struct_0(X3))
                & r2_hidden(X5,sK6)
                & v3_pre_topc(sK6,X1)
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
                    ( ( ~ r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X6)
                      | ~ r1_tmap_1(X1,X0,X2,X5) )
                    & ( r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X6)
                      | r1_tmap_1(X1,X0,X2,X5) )
                    & X5 = X6
                    & r1_tarski(X4,u1_struct_0(sK5))
                    & r2_hidden(X5,X4)
                    & v3_pre_topc(X4,X1)
                    & m1_subset_1(X6,u1_struct_0(sK5)) )
                & m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(sK5,X1)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
                        ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X6)
                          | ~ r1_tmap_1(X1,X0,sK4,X5) )
                        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X6)
                          | r1_tmap_1(X1,X0,sK4,X5) )
                        & X5 = X6
                        & r1_tarski(X4,u1_struct_0(X3))
                        & r2_hidden(X5,X4)
                        & v3_pre_topc(X4,X1)
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
                            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X6)
                              | ~ r1_tmap_1(sK3,X0,X2,X5) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X6)
                              | r1_tmap_1(sK3,X0,X2,X5) )
                            & X5 = X6
                            & r1_tarski(X4,u1_struct_0(X3))
                            & r2_hidden(X5,X4)
                            & v3_pre_topc(X4,sK3)
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,u1_struct_0(sK3)) )
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) )
                & m1_pre_topc(X3,sK3)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
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
                              ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6)
                                | ~ r1_tmap_1(X1,sK2,X2,X5) )
                              & ( r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6)
                                | r1_tmap_1(X1,sK2,X2,X5) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
      | ~ r1_tmap_1(sK3,sK2,sK4,sK7) )
    & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
      | r1_tmap_1(sK3,sK2,sK4,sK7) )
    & sK7 = sK8
    & r1_tarski(sK6,u1_struct_0(sK5))
    & r2_hidden(sK7,sK6)
    & v3_pre_topc(sK6,sK3)
    & m1_subset_1(sK8,u1_struct_0(sK5))
    & m1_subset_1(sK7,u1_struct_0(sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_pre_topc(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f27,f34,f33,f32,f31,f30,f29,f28])).

fof(f54,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f35])).

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
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
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
    inference(flattening,[],[f16])).

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
    inference(nnf_transformation,[],[f17])).

fof(f45,plain,(
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

fof(f69,plain,(
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
    inference(equality_resolution,[],[f45])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
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
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
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
    inference(flattening,[],[f14])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f15])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
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
    inference(equality_resolution,[],[f44])).

fof(f57,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f50,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f49,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | ~ r1_tmap_1(sK3,sK2,sK4,sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | r1_tmap_1(sK3,sK2,sK4,sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
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

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f23,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK1(X0,X1,X4),X1)
        & m1_connsp_2(sK1(X0,X1,X4),X0,X4)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
            | ~ m1_connsp_2(X3,X0,sK0(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,sK0(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ( r1_tarski(sK1(X0,X1,X4),X1)
                    & m1_connsp_2(sK1(X0,X1,X4),X0,X4)
                    & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).

fof(f38,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( m1_connsp_2(sK1(X0,X1,X4),X0,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
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

fof(f68,plain,(
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
    inference(equality_resolution,[],[f46])).

fof(f62,plain,(
    r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    v3_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X4),X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2707,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,X0_54,X1_54)
    | r1_tmap_1(X0_53,X1_53,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_3990,plain,
    ( r1_tmap_1(sK5,sK2,X0_54,X1_54)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | X1_54 != sK7 ),
    inference(instantiation,[status(thm)],[c_2707])).

cnf(c_4368,plain,
    ( r1_tmap_1(sK5,sK2,X0_54,sK8)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK8 != sK7 ),
    inference(instantiation,[status(thm)],[c_3990])).

cnf(c_4564,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK8 != sK7 ),
    inference(instantiation,[status(thm)],[c_4368])).

cnf(c_3995,plain,
    ( r1_tmap_1(sK3,sK2,X0_54,X1_54)
    | ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | X1_54 != sK7
    | X0_54 != sK4 ),
    inference(instantiation,[status(thm)],[c_2707])).

cnf(c_4379,plain,
    ( r1_tmap_1(sK3,sK2,X0_54,sK8)
    | ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | X0_54 != sK4
    | sK8 != sK7 ),
    inference(instantiation,[status(thm)],[c_3995])).

cnf(c_4381,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK3,sK2,sK4,sK8)
    | sK8 != sK7
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4379])).

cnf(c_2699,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_3737,plain,
    ( X0_54 != X1_54
    | X0_54 = sK7
    | sK7 != X1_54 ),
    inference(instantiation,[status(thm)],[c_2699])).

cnf(c_3906,plain,
    ( X0_54 = sK7
    | X0_54 != sK8
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_3737])).

cnf(c_3954,plain,
    ( sK7 != sK8
    | sK8 = sK7
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_3906])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2692,plain,
    ( ~ r1_tarski(X0_54,X1_54)
    | ~ r1_tarski(X2_54,X0_54)
    | r1_tarski(X2_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3639,plain,
    ( r1_tarski(X0_54,u1_struct_0(sK5))
    | ~ r1_tarski(X0_54,sK6)
    | ~ r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2692])).

cnf(c_3897,plain,
    ( r1_tarski(sK1(sK3,sK6,sK7),u1_struct_0(sK5))
    | ~ r1_tarski(sK1(sK3,sK6,sK7),sK6)
    | ~ r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3639])).

cnf(c_2698,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_3835,plain,
    ( k2_tmap_1(sK3,sK2,sK4,sK5) = k2_tmap_1(sK3,sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2698])).

cnf(c_3685,plain,
    ( r1_tmap_1(sK5,sK2,X0_54,X1_54)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | X1_54 != sK8 ),
    inference(instantiation,[status(thm)],[c_2707])).

cnf(c_3769,plain,
    ( r1_tmap_1(sK5,sK2,X0_54,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_3685])).

cnf(c_3834,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_3769])).

cnf(c_3819,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2698])).

cnf(c_2702,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | m1_subset_1(X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_3660,plain,
    ( m1_subset_1(X0_54,X1_54)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | X1_54 != u1_struct_0(sK5)
    | X0_54 != sK8 ),
    inference(instantiation,[status(thm)],[c_2702])).

cnf(c_3718,plain,
    ( m1_subset_1(sK7,X0_54)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | X0_54 != u1_struct_0(sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_3660])).

cnf(c_3818,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_3718])).

cnf(c_3724,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_2698])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f54])).

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
    inference(cnf_transformation,[],[f69])).

cnf(c_8,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_161,plain,
    ( ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_8])).

cnf(c_162,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_161])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_393,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK5 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_162,c_20])).

cnf(c_394,plain,
    ( ~ r1_tmap_1(sK3,X0,X1,X2)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_398,plain,
    ( ~ l1_pre_topc(X0)
    | ~ r1_tmap_1(sK3,X0,X1,X2)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_27,c_26,c_25,c_21])).

cnf(c_399,plain,
    ( ~ r1_tmap_1(sK3,X0,X1,X2)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_398])).

cnf(c_553,plain,
    ( ~ r1_tmap_1(sK3,X0,X1,X2)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_399])).

cnf(c_554,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_558,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tmap_1(sK3,X0,sK4,X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_554,c_24])).

cnf(c_559,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_558])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1236,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_559,c_28])).

cnf(c_1237,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1236])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1241,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1237,c_30,c_29,c_22])).

cnf(c_1242,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1241])).

cnf(c_2033,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1242])).

cnf(c_2668,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0_54)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_2033])).

cnf(c_3631,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2668])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2691,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3339,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2691])).

cnf(c_13,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2689,negated_conjecture,
    ( sK7 = sK8 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_3393,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK8) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3339,c_2689])).

cnf(c_3572,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK8)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3393])).

cnf(c_12,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2690,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3340,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2690])).

cnf(c_3388,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK8) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3340,c_2689])).

cnf(c_3557,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK8)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3388])).

cnf(c_2719,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2698])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | m1_subset_1(sK1(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1326,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | m1_subset_1(sK1(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_25])).

cnf(c_1327,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_pre_topc(X1,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1326])).

cnf(c_1331,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_pre_topc(X1,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1327,c_27,c_26])).

cnf(c_6,plain,
    ( m1_connsp_2(sK1(X0,X1,X2),X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

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
    inference(cnf_transformation,[],[f68])).

cnf(c_435,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK5 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_436,plain,
    ( r1_tmap_1(sK3,X0,X1,X2)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ r1_tarski(X3,u1_struct_0(sK5))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_440,plain,
    ( ~ l1_pre_topc(X0)
    | r1_tmap_1(sK3,X0,X1,X2)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ r1_tarski(X3,u1_struct_0(sK5))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_27,c_26,c_25,c_21])).

cnf(c_441,plain,
    ( r1_tmap_1(sK3,X0,X1,X2)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ r1_tarski(X3,u1_struct_0(sK5))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_440])).

cnf(c_505,plain,
    ( r1_tmap_1(sK3,X0,X1,X2)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
    | ~ m1_connsp_2(X3,sK3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ r1_tarski(X3,u1_struct_0(sK5))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_441])).

cnf(c_506,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_510,plain,
    ( ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | r1_tmap_1(sK3,X0,sK4,X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_24])).

cnf(c_511,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_510])).

cnf(c_641,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r2_hidden(X2,X3)
    | ~ v3_pre_topc(X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X5,u1_struct_0(sK5))
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | X1 != X2
    | sK1(X4,X3,X2) != X5
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | sK3 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_511])).

cnf(c_642,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_646,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(X2,sK3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | r1_tmap_1(sK3,X0,sK4,X1)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_642,c_27,c_26,c_25])).

cnf(c_647,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_646])).

cnf(c_1168,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_647,c_28])).

cnf(c_1169,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r2_hidden(X0,X1)
    | ~ v3_pre_topc(X1,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1168])).

cnf(c_1173,plain,
    ( ~ m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(X1,sK3)
    | ~ r2_hidden(X0,X1)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1169,c_30,c_29,c_22])).

cnf(c_1174,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r2_hidden(X0,X1)
    | ~ v3_pre_topc(X1,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1173])).

cnf(c_1353,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r2_hidden(X0,X1)
    | ~ v3_pre_topc(X1,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1331,c_1174])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1573,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ v3_pre_topc(X1,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK6 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1353,c_15])).

cnf(c_1574,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ v3_pre_topc(sK6,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ r1_tarski(sK1(sK3,sK6,sK7),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_1573])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_16,negated_conjecture,
    ( v3_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1576,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ r1_tarski(sK1(sK3,sK6,sK7),u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1574,c_19,c_18,c_16])).

cnf(c_1577,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ r1_tarski(sK1(sK3,sK6,sK7),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_1576])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | r1_tarski(sK1(X2,X1,X0),X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_915,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_tarski(sK1(X1,X0,X2),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK6 != X0
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_916,plain,
    ( ~ v3_pre_topc(sK6,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK7,u1_struct_0(X0))
    | r1_tarski(sK1(X0,sK6,sK7),sK6)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_915])).

cnf(c_918,plain,
    ( ~ v3_pre_topc(sK6,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | r1_tarski(sK1(sK3,sK6,sK7),sK6)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_916])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4564,c_4381,c_3954,c_3897,c_3835,c_3834,c_3819,c_3818,c_3724,c_3631,c_3572,c_3557,c_2689,c_2719,c_1577,c_918,c_12,c_14,c_16,c_17,c_18,c_19,c_25,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:52:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.78/1.08  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.08  
% 1.78/1.08  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.78/1.08  
% 1.78/1.08  ------  iProver source info
% 1.78/1.08  
% 1.78/1.08  git: date: 2020-06-30 10:37:57 +0100
% 1.78/1.08  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.78/1.08  git: non_committed_changes: false
% 1.78/1.08  git: last_make_outside_of_git: false
% 1.78/1.08  
% 1.78/1.08  ------ 
% 1.78/1.08  
% 1.78/1.08  ------ Input Options
% 1.78/1.08  
% 1.78/1.08  --out_options                           all
% 1.78/1.08  --tptp_safe_out                         true
% 1.78/1.08  --problem_path                          ""
% 1.78/1.08  --include_path                          ""
% 1.78/1.08  --clausifier                            res/vclausify_rel
% 1.78/1.08  --clausifier_options                    --mode clausify
% 1.78/1.08  --stdin                                 false
% 1.78/1.08  --stats_out                             all
% 1.78/1.08  
% 1.78/1.08  ------ General Options
% 1.78/1.08  
% 1.78/1.08  --fof                                   false
% 1.78/1.08  --time_out_real                         305.
% 1.78/1.08  --time_out_virtual                      -1.
% 1.78/1.08  --symbol_type_check                     false
% 1.78/1.08  --clausify_out                          false
% 1.78/1.08  --sig_cnt_out                           false
% 1.78/1.08  --trig_cnt_out                          false
% 1.78/1.08  --trig_cnt_out_tolerance                1.
% 1.78/1.08  --trig_cnt_out_sk_spl                   false
% 1.78/1.08  --abstr_cl_out                          false
% 1.78/1.08  
% 1.78/1.08  ------ Global Options
% 1.78/1.08  
% 1.78/1.08  --schedule                              default
% 1.78/1.08  --add_important_lit                     false
% 1.78/1.08  --prop_solver_per_cl                    1000
% 1.78/1.08  --min_unsat_core                        false
% 1.78/1.08  --soft_assumptions                      false
% 1.78/1.08  --soft_lemma_size                       3
% 1.78/1.08  --prop_impl_unit_size                   0
% 1.78/1.08  --prop_impl_unit                        []
% 1.78/1.08  --share_sel_clauses                     true
% 1.78/1.08  --reset_solvers                         false
% 1.78/1.08  --bc_imp_inh                            [conj_cone]
% 1.78/1.08  --conj_cone_tolerance                   3.
% 1.78/1.08  --extra_neg_conj                        none
% 1.78/1.08  --large_theory_mode                     true
% 1.78/1.08  --prolific_symb_bound                   200
% 1.78/1.08  --lt_threshold                          2000
% 1.78/1.08  --clause_weak_htbl                      true
% 1.78/1.08  --gc_record_bc_elim                     false
% 1.78/1.08  
% 1.78/1.08  ------ Preprocessing Options
% 1.78/1.08  
% 1.78/1.08  --preprocessing_flag                    true
% 1.78/1.08  --time_out_prep_mult                    0.1
% 1.78/1.08  --splitting_mode                        input
% 1.78/1.08  --splitting_grd                         true
% 1.78/1.08  --splitting_cvd                         false
% 1.78/1.08  --splitting_cvd_svl                     false
% 1.78/1.08  --splitting_nvd                         32
% 1.78/1.08  --sub_typing                            true
% 1.78/1.08  --prep_gs_sim                           true
% 1.78/1.08  --prep_unflatten                        true
% 1.78/1.08  --prep_res_sim                          true
% 1.78/1.08  --prep_upred                            true
% 1.78/1.08  --prep_sem_filter                       exhaustive
% 1.78/1.08  --prep_sem_filter_out                   false
% 1.78/1.08  --pred_elim                             true
% 1.78/1.08  --res_sim_input                         true
% 1.78/1.08  --eq_ax_congr_red                       true
% 1.78/1.08  --pure_diseq_elim                       true
% 1.78/1.08  --brand_transform                       false
% 1.78/1.08  --non_eq_to_eq                          false
% 1.78/1.08  --prep_def_merge                        true
% 1.78/1.08  --prep_def_merge_prop_impl              false
% 1.78/1.08  --prep_def_merge_mbd                    true
% 1.78/1.08  --prep_def_merge_tr_red                 false
% 1.78/1.08  --prep_def_merge_tr_cl                  false
% 1.78/1.08  --smt_preprocessing                     true
% 1.78/1.08  --smt_ac_axioms                         fast
% 1.78/1.08  --preprocessed_out                      false
% 1.78/1.08  --preprocessed_stats                    false
% 1.78/1.08  
% 1.78/1.08  ------ Abstraction refinement Options
% 1.78/1.08  
% 1.78/1.08  --abstr_ref                             []
% 1.78/1.08  --abstr_ref_prep                        false
% 1.78/1.08  --abstr_ref_until_sat                   false
% 1.78/1.08  --abstr_ref_sig_restrict                funpre
% 1.78/1.08  --abstr_ref_af_restrict_to_split_sk     false
% 1.78/1.08  --abstr_ref_under                       []
% 1.78/1.08  
% 1.78/1.08  ------ SAT Options
% 1.78/1.08  
% 1.78/1.08  --sat_mode                              false
% 1.78/1.08  --sat_fm_restart_options                ""
% 1.78/1.08  --sat_gr_def                            false
% 1.78/1.08  --sat_epr_types                         true
% 1.78/1.08  --sat_non_cyclic_types                  false
% 1.78/1.08  --sat_finite_models                     false
% 1.78/1.08  --sat_fm_lemmas                         false
% 1.78/1.08  --sat_fm_prep                           false
% 1.78/1.08  --sat_fm_uc_incr                        true
% 1.78/1.08  --sat_out_model                         small
% 1.78/1.08  --sat_out_clauses                       false
% 1.78/1.08  
% 1.78/1.08  ------ QBF Options
% 1.78/1.08  
% 1.78/1.08  --qbf_mode                              false
% 1.78/1.08  --qbf_elim_univ                         false
% 1.78/1.08  --qbf_dom_inst                          none
% 1.78/1.08  --qbf_dom_pre_inst                      false
% 1.78/1.08  --qbf_sk_in                             false
% 1.78/1.08  --qbf_pred_elim                         true
% 1.78/1.08  --qbf_split                             512
% 1.78/1.08  
% 1.78/1.08  ------ BMC1 Options
% 1.78/1.08  
% 1.78/1.08  --bmc1_incremental                      false
% 1.78/1.08  --bmc1_axioms                           reachable_all
% 1.78/1.08  --bmc1_min_bound                        0
% 1.78/1.08  --bmc1_max_bound                        -1
% 1.78/1.08  --bmc1_max_bound_default                -1
% 1.78/1.08  --bmc1_symbol_reachability              true
% 1.78/1.08  --bmc1_property_lemmas                  false
% 1.78/1.08  --bmc1_k_induction                      false
% 1.78/1.08  --bmc1_non_equiv_states                 false
% 1.78/1.08  --bmc1_deadlock                         false
% 1.78/1.08  --bmc1_ucm                              false
% 1.78/1.08  --bmc1_add_unsat_core                   none
% 1.78/1.08  --bmc1_unsat_core_children              false
% 1.78/1.08  --bmc1_unsat_core_extrapolate_axioms    false
% 1.78/1.08  --bmc1_out_stat                         full
% 1.78/1.08  --bmc1_ground_init                      false
% 1.78/1.08  --bmc1_pre_inst_next_state              false
% 1.78/1.08  --bmc1_pre_inst_state                   false
% 1.78/1.08  --bmc1_pre_inst_reach_state             false
% 1.78/1.08  --bmc1_out_unsat_core                   false
% 1.78/1.08  --bmc1_aig_witness_out                  false
% 1.78/1.08  --bmc1_verbose                          false
% 1.78/1.08  --bmc1_dump_clauses_tptp                false
% 1.78/1.08  --bmc1_dump_unsat_core_tptp             false
% 1.78/1.08  --bmc1_dump_file                        -
% 1.78/1.08  --bmc1_ucm_expand_uc_limit              128
% 1.78/1.08  --bmc1_ucm_n_expand_iterations          6
% 1.78/1.08  --bmc1_ucm_extend_mode                  1
% 1.78/1.08  --bmc1_ucm_init_mode                    2
% 1.78/1.08  --bmc1_ucm_cone_mode                    none
% 1.78/1.08  --bmc1_ucm_reduced_relation_type        0
% 1.78/1.08  --bmc1_ucm_relax_model                  4
% 1.78/1.08  --bmc1_ucm_full_tr_after_sat            true
% 1.78/1.08  --bmc1_ucm_expand_neg_assumptions       false
% 1.78/1.08  --bmc1_ucm_layered_model                none
% 1.78/1.08  --bmc1_ucm_max_lemma_size               10
% 1.78/1.08  
% 1.78/1.08  ------ AIG Options
% 1.78/1.08  
% 1.78/1.08  --aig_mode                              false
% 1.78/1.08  
% 1.78/1.08  ------ Instantiation Options
% 1.78/1.08  
% 1.78/1.08  --instantiation_flag                    true
% 1.78/1.08  --inst_sos_flag                         false
% 1.78/1.08  --inst_sos_phase                        true
% 1.78/1.08  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.78/1.08  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.78/1.08  --inst_lit_sel_side                     num_symb
% 1.78/1.08  --inst_solver_per_active                1400
% 1.78/1.08  --inst_solver_calls_frac                1.
% 1.78/1.08  --inst_passive_queue_type               priority_queues
% 1.78/1.08  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.78/1.08  --inst_passive_queues_freq              [25;2]
% 1.78/1.08  --inst_dismatching                      true
% 1.78/1.08  --inst_eager_unprocessed_to_passive     true
% 1.78/1.08  --inst_prop_sim_given                   true
% 1.78/1.08  --inst_prop_sim_new                     false
% 1.78/1.08  --inst_subs_new                         false
% 1.78/1.08  --inst_eq_res_simp                      false
% 1.78/1.08  --inst_subs_given                       false
% 1.78/1.08  --inst_orphan_elimination               true
% 1.78/1.08  --inst_learning_loop_flag               true
% 1.78/1.08  --inst_learning_start                   3000
% 1.78/1.08  --inst_learning_factor                  2
% 1.78/1.08  --inst_start_prop_sim_after_learn       3
% 1.78/1.08  --inst_sel_renew                        solver
% 1.78/1.08  --inst_lit_activity_flag                true
% 1.78/1.08  --inst_restr_to_given                   false
% 1.78/1.08  --inst_activity_threshold               500
% 1.78/1.08  --inst_out_proof                        true
% 1.78/1.08  
% 1.78/1.08  ------ Resolution Options
% 1.78/1.08  
% 1.78/1.08  --resolution_flag                       true
% 1.78/1.08  --res_lit_sel                           adaptive
% 1.78/1.08  --res_lit_sel_side                      none
% 1.78/1.08  --res_ordering                          kbo
% 1.78/1.08  --res_to_prop_solver                    active
% 1.78/1.08  --res_prop_simpl_new                    false
% 1.78/1.08  --res_prop_simpl_given                  true
% 1.78/1.08  --res_passive_queue_type                priority_queues
% 1.78/1.08  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.78/1.08  --res_passive_queues_freq               [15;5]
% 1.78/1.08  --res_forward_subs                      full
% 1.78/1.08  --res_backward_subs                     full
% 1.78/1.08  --res_forward_subs_resolution           true
% 1.78/1.08  --res_backward_subs_resolution          true
% 1.78/1.08  --res_orphan_elimination                true
% 1.78/1.08  --res_time_limit                        2.
% 1.78/1.08  --res_out_proof                         true
% 1.78/1.08  
% 1.78/1.08  ------ Superposition Options
% 1.78/1.08  
% 1.78/1.08  --superposition_flag                    true
% 1.78/1.08  --sup_passive_queue_type                priority_queues
% 1.78/1.08  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.78/1.08  --sup_passive_queues_freq               [8;1;4]
% 1.78/1.08  --demod_completeness_check              fast
% 1.78/1.08  --demod_use_ground                      true
% 1.78/1.08  --sup_to_prop_solver                    passive
% 1.78/1.08  --sup_prop_simpl_new                    true
% 1.78/1.08  --sup_prop_simpl_given                  true
% 1.78/1.08  --sup_fun_splitting                     false
% 1.78/1.08  --sup_smt_interval                      50000
% 1.78/1.08  
% 1.78/1.08  ------ Superposition Simplification Setup
% 1.78/1.08  
% 1.78/1.08  --sup_indices_passive                   []
% 1.78/1.08  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/1.08  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/1.08  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/1.08  --sup_full_triv                         [TrivRules;PropSubs]
% 1.78/1.08  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/1.08  --sup_full_bw                           [BwDemod]
% 1.78/1.08  --sup_immed_triv                        [TrivRules]
% 1.78/1.08  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.78/1.08  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/1.08  --sup_immed_bw_main                     []
% 1.78/1.08  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/1.08  --sup_input_triv                        [Unflattening;TrivRules]
% 1.78/1.08  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/1.08  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/1.08  
% 1.78/1.08  ------ Combination Options
% 1.78/1.08  
% 1.78/1.08  --comb_res_mult                         3
% 1.78/1.08  --comb_sup_mult                         2
% 1.78/1.08  --comb_inst_mult                        10
% 1.78/1.08  
% 1.78/1.08  ------ Debug Options
% 1.78/1.08  
% 1.78/1.08  --dbg_backtrace                         false
% 1.78/1.08  --dbg_dump_prop_clauses                 false
% 1.78/1.08  --dbg_dump_prop_clauses_file            -
% 1.78/1.08  --dbg_out_stat                          false
% 1.78/1.08  ------ Parsing...
% 1.78/1.08  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.78/1.08  
% 1.78/1.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.78/1.08  
% 1.78/1.08  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.78/1.08  
% 1.78/1.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.78/1.08  ------ Proving...
% 1.78/1.08  ------ Problem Properties 
% 1.78/1.08  
% 1.78/1.08  
% 1.78/1.08  clauses                                 27
% 1.78/1.08  conjectures                             10
% 1.78/1.08  EPR                                     4
% 1.78/1.08  Horn                                    22
% 1.78/1.08  unary                                   8
% 1.78/1.08  binary                                  2
% 1.78/1.08  lits                                    91
% 1.78/1.08  lits eq                                 3
% 1.78/1.08  fd_pure                                 0
% 1.78/1.08  fd_pseudo                               0
% 1.78/1.08  fd_cond                                 0
% 1.78/1.08  fd_pseudo_cond                          0
% 1.78/1.08  AC symbols                              0
% 1.78/1.08  
% 1.78/1.08  ------ Schedule dynamic 5 is on 
% 1.78/1.08  
% 1.78/1.08  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.78/1.08  
% 1.78/1.08  
% 1.78/1.08  ------ 
% 1.78/1.08  Current options:
% 1.78/1.08  ------ 
% 1.78/1.08  
% 1.78/1.08  ------ Input Options
% 1.78/1.08  
% 1.78/1.08  --out_options                           all
% 1.78/1.08  --tptp_safe_out                         true
% 1.78/1.08  --problem_path                          ""
% 1.78/1.08  --include_path                          ""
% 1.78/1.08  --clausifier                            res/vclausify_rel
% 1.78/1.08  --clausifier_options                    --mode clausify
% 1.78/1.08  --stdin                                 false
% 1.78/1.08  --stats_out                             all
% 1.78/1.08  
% 1.78/1.08  ------ General Options
% 1.78/1.08  
% 1.78/1.08  --fof                                   false
% 1.78/1.08  --time_out_real                         305.
% 1.78/1.08  --time_out_virtual                      -1.
% 1.78/1.08  --symbol_type_check                     false
% 1.78/1.08  --clausify_out                          false
% 1.78/1.08  --sig_cnt_out                           false
% 1.78/1.08  --trig_cnt_out                          false
% 1.78/1.08  --trig_cnt_out_tolerance                1.
% 1.78/1.08  --trig_cnt_out_sk_spl                   false
% 1.78/1.08  --abstr_cl_out                          false
% 1.78/1.08  
% 1.78/1.08  ------ Global Options
% 1.78/1.08  
% 1.78/1.08  --schedule                              default
% 1.78/1.08  --add_important_lit                     false
% 1.78/1.08  --prop_solver_per_cl                    1000
% 1.78/1.08  --min_unsat_core                        false
% 1.78/1.08  --soft_assumptions                      false
% 1.78/1.08  --soft_lemma_size                       3
% 1.78/1.08  --prop_impl_unit_size                   0
% 1.78/1.08  --prop_impl_unit                        []
% 1.78/1.08  --share_sel_clauses                     true
% 1.78/1.08  --reset_solvers                         false
% 1.78/1.08  --bc_imp_inh                            [conj_cone]
% 1.78/1.08  --conj_cone_tolerance                   3.
% 1.78/1.08  --extra_neg_conj                        none
% 1.78/1.08  --large_theory_mode                     true
% 1.78/1.08  --prolific_symb_bound                   200
% 1.78/1.08  --lt_threshold                          2000
% 1.78/1.08  --clause_weak_htbl                      true
% 1.78/1.08  --gc_record_bc_elim                     false
% 1.78/1.08  
% 1.78/1.08  ------ Preprocessing Options
% 1.78/1.08  
% 1.78/1.08  --preprocessing_flag                    true
% 1.78/1.08  --time_out_prep_mult                    0.1
% 1.78/1.08  --splitting_mode                        input
% 1.78/1.08  --splitting_grd                         true
% 1.78/1.08  --splitting_cvd                         false
% 1.78/1.08  --splitting_cvd_svl                     false
% 1.78/1.08  --splitting_nvd                         32
% 1.78/1.08  --sub_typing                            true
% 1.78/1.08  --prep_gs_sim                           true
% 1.78/1.08  --prep_unflatten                        true
% 1.78/1.08  --prep_res_sim                          true
% 1.78/1.08  --prep_upred                            true
% 1.78/1.08  --prep_sem_filter                       exhaustive
% 1.78/1.08  --prep_sem_filter_out                   false
% 1.78/1.08  --pred_elim                             true
% 1.78/1.08  --res_sim_input                         true
% 1.78/1.08  --eq_ax_congr_red                       true
% 1.78/1.08  --pure_diseq_elim                       true
% 1.78/1.08  --brand_transform                       false
% 1.78/1.08  --non_eq_to_eq                          false
% 1.78/1.08  --prep_def_merge                        true
% 1.78/1.08  --prep_def_merge_prop_impl              false
% 1.78/1.08  --prep_def_merge_mbd                    true
% 1.78/1.08  --prep_def_merge_tr_red                 false
% 1.78/1.08  --prep_def_merge_tr_cl                  false
% 1.78/1.08  --smt_preprocessing                     true
% 1.78/1.08  --smt_ac_axioms                         fast
% 1.78/1.08  --preprocessed_out                      false
% 1.78/1.08  --preprocessed_stats                    false
% 1.78/1.08  
% 1.78/1.08  ------ Abstraction refinement Options
% 1.78/1.08  
% 1.78/1.08  --abstr_ref                             []
% 1.78/1.08  --abstr_ref_prep                        false
% 1.78/1.08  --abstr_ref_until_sat                   false
% 1.78/1.08  --abstr_ref_sig_restrict                funpre
% 1.78/1.08  --abstr_ref_af_restrict_to_split_sk     false
% 1.78/1.08  --abstr_ref_under                       []
% 1.78/1.08  
% 1.78/1.08  ------ SAT Options
% 1.78/1.08  
% 1.78/1.08  --sat_mode                              false
% 1.78/1.08  --sat_fm_restart_options                ""
% 1.78/1.08  --sat_gr_def                            false
% 1.78/1.08  --sat_epr_types                         true
% 1.78/1.08  --sat_non_cyclic_types                  false
% 1.78/1.08  --sat_finite_models                     false
% 1.78/1.08  --sat_fm_lemmas                         false
% 1.78/1.08  --sat_fm_prep                           false
% 1.78/1.08  --sat_fm_uc_incr                        true
% 1.78/1.08  --sat_out_model                         small
% 1.78/1.08  --sat_out_clauses                       false
% 1.78/1.08  
% 1.78/1.08  ------ QBF Options
% 1.78/1.08  
% 1.78/1.08  --qbf_mode                              false
% 1.78/1.08  --qbf_elim_univ                         false
% 1.78/1.08  --qbf_dom_inst                          none
% 1.78/1.08  --qbf_dom_pre_inst                      false
% 1.78/1.08  --qbf_sk_in                             false
% 1.78/1.08  --qbf_pred_elim                         true
% 1.78/1.08  --qbf_split                             512
% 1.78/1.08  
% 1.78/1.08  ------ BMC1 Options
% 1.78/1.08  
% 1.78/1.08  --bmc1_incremental                      false
% 1.78/1.08  --bmc1_axioms                           reachable_all
% 1.78/1.08  --bmc1_min_bound                        0
% 1.78/1.08  --bmc1_max_bound                        -1
% 1.78/1.08  --bmc1_max_bound_default                -1
% 1.78/1.08  --bmc1_symbol_reachability              true
% 1.78/1.08  --bmc1_property_lemmas                  false
% 1.78/1.08  --bmc1_k_induction                      false
% 1.78/1.08  --bmc1_non_equiv_states                 false
% 1.78/1.08  --bmc1_deadlock                         false
% 1.78/1.08  --bmc1_ucm                              false
% 1.78/1.08  --bmc1_add_unsat_core                   none
% 1.78/1.08  --bmc1_unsat_core_children              false
% 1.78/1.08  --bmc1_unsat_core_extrapolate_axioms    false
% 1.78/1.08  --bmc1_out_stat                         full
% 1.78/1.08  --bmc1_ground_init                      false
% 1.78/1.08  --bmc1_pre_inst_next_state              false
% 1.78/1.08  --bmc1_pre_inst_state                   false
% 1.78/1.08  --bmc1_pre_inst_reach_state             false
% 1.78/1.08  --bmc1_out_unsat_core                   false
% 1.78/1.08  --bmc1_aig_witness_out                  false
% 1.78/1.08  --bmc1_verbose                          false
% 1.78/1.08  --bmc1_dump_clauses_tptp                false
% 1.78/1.08  --bmc1_dump_unsat_core_tptp             false
% 1.78/1.08  --bmc1_dump_file                        -
% 1.78/1.08  --bmc1_ucm_expand_uc_limit              128
% 1.78/1.08  --bmc1_ucm_n_expand_iterations          6
% 1.78/1.08  --bmc1_ucm_extend_mode                  1
% 1.78/1.08  --bmc1_ucm_init_mode                    2
% 1.78/1.08  --bmc1_ucm_cone_mode                    none
% 1.78/1.08  --bmc1_ucm_reduced_relation_type        0
% 1.78/1.08  --bmc1_ucm_relax_model                  4
% 1.78/1.08  --bmc1_ucm_full_tr_after_sat            true
% 1.78/1.08  --bmc1_ucm_expand_neg_assumptions       false
% 1.78/1.08  --bmc1_ucm_layered_model                none
% 1.78/1.08  --bmc1_ucm_max_lemma_size               10
% 1.78/1.08  
% 1.78/1.08  ------ AIG Options
% 1.78/1.08  
% 1.78/1.08  --aig_mode                              false
% 1.78/1.08  
% 1.78/1.08  ------ Instantiation Options
% 1.78/1.08  
% 1.78/1.08  --instantiation_flag                    true
% 1.78/1.08  --inst_sos_flag                         false
% 1.78/1.08  --inst_sos_phase                        true
% 1.78/1.08  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.78/1.08  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.78/1.08  --inst_lit_sel_side                     none
% 1.78/1.08  --inst_solver_per_active                1400
% 1.78/1.08  --inst_solver_calls_frac                1.
% 1.78/1.08  --inst_passive_queue_type               priority_queues
% 1.78/1.08  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.78/1.08  --inst_passive_queues_freq              [25;2]
% 1.78/1.08  --inst_dismatching                      true
% 1.78/1.08  --inst_eager_unprocessed_to_passive     true
% 1.78/1.08  --inst_prop_sim_given                   true
% 1.78/1.08  --inst_prop_sim_new                     false
% 1.78/1.08  --inst_subs_new                         false
% 1.78/1.08  --inst_eq_res_simp                      false
% 1.78/1.08  --inst_subs_given                       false
% 1.78/1.08  --inst_orphan_elimination               true
% 1.78/1.08  --inst_learning_loop_flag               true
% 1.78/1.08  --inst_learning_start                   3000
% 1.78/1.08  --inst_learning_factor                  2
% 1.78/1.08  --inst_start_prop_sim_after_learn       3
% 1.78/1.08  --inst_sel_renew                        solver
% 1.78/1.08  --inst_lit_activity_flag                true
% 1.78/1.08  --inst_restr_to_given                   false
% 1.78/1.08  --inst_activity_threshold               500
% 1.78/1.08  --inst_out_proof                        true
% 1.78/1.08  
% 1.78/1.08  ------ Resolution Options
% 1.78/1.08  
% 1.78/1.08  --resolution_flag                       false
% 1.78/1.08  --res_lit_sel                           adaptive
% 1.78/1.08  --res_lit_sel_side                      none
% 1.78/1.08  --res_ordering                          kbo
% 1.78/1.08  --res_to_prop_solver                    active
% 1.78/1.08  --res_prop_simpl_new                    false
% 1.78/1.08  --res_prop_simpl_given                  true
% 1.78/1.08  --res_passive_queue_type                priority_queues
% 1.78/1.08  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.78/1.08  --res_passive_queues_freq               [15;5]
% 1.78/1.08  --res_forward_subs                      full
% 1.78/1.08  --res_backward_subs                     full
% 1.78/1.08  --res_forward_subs_resolution           true
% 1.78/1.08  --res_backward_subs_resolution          true
% 1.78/1.08  --res_orphan_elimination                true
% 1.78/1.08  --res_time_limit                        2.
% 1.78/1.08  --res_out_proof                         true
% 1.78/1.08  
% 1.78/1.08  ------ Superposition Options
% 1.78/1.08  
% 1.78/1.08  --superposition_flag                    true
% 1.78/1.08  --sup_passive_queue_type                priority_queues
% 1.78/1.08  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.78/1.08  --sup_passive_queues_freq               [8;1;4]
% 1.78/1.08  --demod_completeness_check              fast
% 1.78/1.08  --demod_use_ground                      true
% 1.78/1.08  --sup_to_prop_solver                    passive
% 1.78/1.08  --sup_prop_simpl_new                    true
% 1.78/1.08  --sup_prop_simpl_given                  true
% 1.78/1.08  --sup_fun_splitting                     false
% 1.78/1.08  --sup_smt_interval                      50000
% 1.78/1.08  
% 1.78/1.08  ------ Superposition Simplification Setup
% 1.78/1.08  
% 1.78/1.08  --sup_indices_passive                   []
% 1.78/1.08  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/1.08  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/1.08  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/1.08  --sup_full_triv                         [TrivRules;PropSubs]
% 1.78/1.08  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/1.08  --sup_full_bw                           [BwDemod]
% 1.78/1.08  --sup_immed_triv                        [TrivRules]
% 1.78/1.08  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.78/1.08  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/1.08  --sup_immed_bw_main                     []
% 1.78/1.08  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/1.08  --sup_input_triv                        [Unflattening;TrivRules]
% 1.78/1.08  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/1.08  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/1.08  
% 1.78/1.08  ------ Combination Options
% 1.78/1.08  
% 1.78/1.08  --comb_res_mult                         3
% 1.78/1.08  --comb_sup_mult                         2
% 1.78/1.08  --comb_inst_mult                        10
% 1.78/1.08  
% 1.78/1.08  ------ Debug Options
% 1.78/1.08  
% 1.78/1.08  --dbg_backtrace                         false
% 1.78/1.08  --dbg_dump_prop_clauses                 false
% 1.78/1.08  --dbg_dump_prop_clauses_file            -
% 1.78/1.08  --dbg_out_stat                          false
% 1.78/1.08  
% 1.78/1.08  
% 1.78/1.08  
% 1.78/1.08  
% 1.78/1.08  ------ Proving...
% 1.78/1.08  
% 1.78/1.08  
% 1.78/1.08  % SZS status Theorem for theBenchmark.p
% 1.78/1.08  
% 1.78/1.08  % SZS output start CNFRefutation for theBenchmark.p
% 1.78/1.08  
% 1.78/1.08  fof(f1,axiom,(
% 1.78/1.08    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.78/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.78/1.08  
% 1.78/1.08  fof(f8,plain,(
% 1.78/1.08    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.78/1.08    inference(ennf_transformation,[],[f1])).
% 1.78/1.08  
% 1.78/1.08  fof(f9,plain,(
% 1.78/1.08    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.78/1.08    inference(flattening,[],[f8])).
% 1.78/1.08  
% 1.78/1.08  fof(f36,plain,(
% 1.78/1.08    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.78/1.08    inference(cnf_transformation,[],[f9])).
% 1.78/1.08  
% 1.78/1.08  fof(f6,conjecture,(
% 1.78/1.08    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.78/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.78/1.08  
% 1.78/1.08  fof(f7,negated_conjecture,(
% 1.78/1.08    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.78/1.08    inference(negated_conjecture,[],[f6])).
% 1.78/1.08  
% 1.78/1.08  fof(f18,plain,(
% 1.78/1.08    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.78/1.08    inference(ennf_transformation,[],[f7])).
% 1.78/1.08  
% 1.78/1.08  fof(f19,plain,(
% 1.78/1.08    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.78/1.08    inference(flattening,[],[f18])).
% 1.78/1.08  
% 1.78/1.08  fof(f26,plain,(
% 1.78/1.08    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5))) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.78/1.08    inference(nnf_transformation,[],[f19])).
% 1.78/1.08  
% 1.78/1.08  fof(f27,plain,(
% 1.78/1.08    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.78/1.08    inference(flattening,[],[f26])).
% 1.78/1.08  
% 1.78/1.08  fof(f34,plain,(
% 1.78/1.08    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8) | r1_tmap_1(X1,X0,X2,X5)) & sK8 = X5 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(sK8,u1_struct_0(X3)))) )),
% 1.78/1.08    introduced(choice_axiom,[])).
% 1.78/1.08  
% 1.78/1.08  fof(f33,plain,(
% 1.78/1.08    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,sK7)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,sK7)) & sK7 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(sK7,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK7,u1_struct_0(X1)))) )),
% 1.78/1.08    introduced(choice_axiom,[])).
% 1.78/1.08  
% 1.78/1.08  fof(f32,plain,(
% 1.78/1.08    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(sK6,u1_struct_0(X3)) & r2_hidden(X5,sK6) & v3_pre_topc(sK6,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 1.78/1.08    introduced(choice_axiom,[])).
% 1.78/1.08  
% 1.78/1.08  fof(f31,plain,(
% 1.78/1.08    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(sK5)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK5,X1) & ~v2_struct_0(sK5))) )),
% 1.78/1.08    introduced(choice_axiom,[])).
% 1.78/1.08  
% 1.78/1.08  fof(f30,plain,(
% 1.78/1.08    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X6) | ~r1_tmap_1(X1,X0,sK4,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X6) | r1_tmap_1(X1,X0,sK4,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 1.78/1.08    introduced(choice_axiom,[])).
% 1.78/1.08  
% 1.78/1.08  fof(f29,plain,(
% 1.78/1.08    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X6) | ~r1_tmap_1(sK3,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X6) | r1_tmap_1(sK3,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK3) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 1.78/1.08    introduced(choice_axiom,[])).
% 1.78/1.08  
% 1.78/1.08  fof(f28,plain,(
% 1.78/1.08    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6) | ~r1_tmap_1(X1,sK2,X2,X5)) & (r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6) | r1_tmap_1(X1,sK2,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.78/1.08    introduced(choice_axiom,[])).
% 1.78/1.08  
% 1.78/1.08  fof(f35,plain,(
% 1.78/1.08    (((((((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | ~r1_tmap_1(sK3,sK2,sK4,sK7)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | r1_tmap_1(sK3,sK2,sK4,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK5)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK3) & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.78/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f27,f34,f33,f32,f31,f30,f29,f28])).
% 1.78/1.08  
% 1.78/1.08  fof(f54,plain,(
% 1.78/1.08    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f5,axiom,(
% 1.78/1.08    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.78/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.78/1.08  
% 1.78/1.08  fof(f16,plain,(
% 1.78/1.08    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/1.08    inference(ennf_transformation,[],[f5])).
% 1.78/1.08  
% 1.78/1.08  fof(f17,plain,(
% 1.78/1.08    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/1.08    inference(flattening,[],[f16])).
% 1.78/1.08  
% 1.78/1.08  fof(f25,plain,(
% 1.78/1.08    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/1.08    inference(nnf_transformation,[],[f17])).
% 1.78/1.08  
% 1.78/1.08  fof(f45,plain,(
% 1.78/1.08    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/1.08    inference(cnf_transformation,[],[f25])).
% 1.78/1.08  
% 1.78/1.08  fof(f69,plain,(
% 1.78/1.08    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/1.08    inference(equality_resolution,[],[f45])).
% 1.78/1.08  
% 1.78/1.08  fof(f4,axiom,(
% 1.78/1.08    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 1.78/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.78/1.08  
% 1.78/1.08  fof(f14,plain,(
% 1.78/1.08    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/1.08    inference(ennf_transformation,[],[f4])).
% 1.78/1.08  
% 1.78/1.08  fof(f15,plain,(
% 1.78/1.08    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/1.08    inference(flattening,[],[f14])).
% 1.78/1.08  
% 1.78/1.08  fof(f44,plain,(
% 1.78/1.08    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/1.08    inference(cnf_transformation,[],[f15])).
% 1.78/1.08  
% 1.78/1.08  fof(f67,plain,(
% 1.78/1.08    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/1.08    inference(equality_resolution,[],[f44])).
% 1.78/1.08  
% 1.78/1.08  fof(f57,plain,(
% 1.78/1.08    m1_pre_topc(sK5,sK3)),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f50,plain,(
% 1.78/1.08    ~v2_struct_0(sK3)),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f51,plain,(
% 1.78/1.08    v2_pre_topc(sK3)),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f52,plain,(
% 1.78/1.08    l1_pre_topc(sK3)),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f56,plain,(
% 1.78/1.08    ~v2_struct_0(sK5)),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f53,plain,(
% 1.78/1.08    v1_funct_1(sK4)),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f49,plain,(
% 1.78/1.08    l1_pre_topc(sK2)),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f47,plain,(
% 1.78/1.08    ~v2_struct_0(sK2)),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f48,plain,(
% 1.78/1.08    v2_pre_topc(sK2)),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f55,plain,(
% 1.78/1.08    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f66,plain,(
% 1.78/1.08    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | ~r1_tmap_1(sK3,sK2,sK4,sK7)),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f64,plain,(
% 1.78/1.08    sK7 = sK8),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f65,plain,(
% 1.78/1.08    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | r1_tmap_1(sK3,sK2,sK4,sK7)),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f3,axiom,(
% 1.78/1.08    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 1.78/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.78/1.08  
% 1.78/1.08  fof(f12,plain,(
% 1.78/1.08    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/1.08    inference(ennf_transformation,[],[f3])).
% 1.78/1.08  
% 1.78/1.08  fof(f13,plain,(
% 1.78/1.08    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/1.08    inference(flattening,[],[f12])).
% 1.78/1.08  
% 1.78/1.08  fof(f20,plain,(
% 1.78/1.08    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/1.08    inference(nnf_transformation,[],[f13])).
% 1.78/1.08  
% 1.78/1.08  fof(f21,plain,(
% 1.78/1.08    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/1.08    inference(rectify,[],[f20])).
% 1.78/1.08  
% 1.78/1.08  fof(f23,plain,(
% 1.78/1.08    ! [X4,X1,X0] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK1(X0,X1,X4),X1) & m1_connsp_2(sK1(X0,X1,X4),X0,X4) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.78/1.08    introduced(choice_axiom,[])).
% 1.78/1.08  
% 1.78/1.08  fof(f22,plain,(
% 1.78/1.08    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK0(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 1.78/1.08    introduced(choice_axiom,[])).
% 1.78/1.08  
% 1.78/1.08  fof(f24,plain,(
% 1.78/1.08    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK0(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X4] : ((r1_tarski(sK1(X0,X1,X4),X1) & m1_connsp_2(sK1(X0,X1,X4),X0,X4) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).
% 1.78/1.08  
% 1.78/1.08  fof(f38,plain,(
% 1.78/1.08    ( ! [X4,X0,X1] : (m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/1.08    inference(cnf_transformation,[],[f24])).
% 1.78/1.08  
% 1.78/1.08  fof(f39,plain,(
% 1.78/1.08    ( ! [X4,X0,X1] : (m1_connsp_2(sK1(X0,X1,X4),X0,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/1.08    inference(cnf_transformation,[],[f24])).
% 1.78/1.08  
% 1.78/1.08  fof(f46,plain,(
% 1.78/1.08    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/1.08    inference(cnf_transformation,[],[f25])).
% 1.78/1.08  
% 1.78/1.08  fof(f68,plain,(
% 1.78/1.08    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/1.08    inference(equality_resolution,[],[f46])).
% 1.78/1.08  
% 1.78/1.08  fof(f62,plain,(
% 1.78/1.08    r2_hidden(sK7,sK6)),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f58,plain,(
% 1.78/1.08    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f59,plain,(
% 1.78/1.08    m1_subset_1(sK7,u1_struct_0(sK3))),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f61,plain,(
% 1.78/1.08    v3_pre_topc(sK6,sK3)),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f40,plain,(
% 1.78/1.08    ( ! [X4,X0,X1] : (r1_tarski(sK1(X0,X1,X4),X1) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/1.08    inference(cnf_transformation,[],[f24])).
% 1.78/1.08  
% 1.78/1.08  fof(f63,plain,(
% 1.78/1.08    r1_tarski(sK6,u1_struct_0(sK5))),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  fof(f60,plain,(
% 1.78/1.08    m1_subset_1(sK8,u1_struct_0(sK5))),
% 1.78/1.08    inference(cnf_transformation,[],[f35])).
% 1.78/1.08  
% 1.78/1.08  cnf(c_2707,plain,
% 1.78/1.08      ( ~ r1_tmap_1(X0_53,X1_53,X0_54,X1_54)
% 1.78/1.08      | r1_tmap_1(X0_53,X1_53,X2_54,X3_54)
% 1.78/1.08      | X2_54 != X0_54
% 1.78/1.08      | X3_54 != X1_54 ),
% 1.78/1.08      theory(equality) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3990,plain,
% 1.78/1.08      ( r1_tmap_1(sK5,sK2,X0_54,X1_54)
% 1.78/1.08      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 1.78/1.08      | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 1.78/1.08      | X1_54 != sK7 ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_2707]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_4368,plain,
% 1.78/1.08      ( r1_tmap_1(sK5,sK2,X0_54,sK8)
% 1.78/1.08      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 1.78/1.08      | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 1.78/1.08      | sK8 != sK7 ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_3990]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_4564,plain,
% 1.78/1.08      ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 1.78/1.08      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 1.78/1.08      | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
% 1.78/1.08      | sK8 != sK7 ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_4368]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3995,plain,
% 1.78/1.08      ( r1_tmap_1(sK3,sK2,X0_54,X1_54)
% 1.78/1.08      | ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 1.78/1.08      | X1_54 != sK7
% 1.78/1.08      | X0_54 != sK4 ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_2707]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_4379,plain,
% 1.78/1.08      ( r1_tmap_1(sK3,sK2,X0_54,sK8)
% 1.78/1.08      | ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 1.78/1.08      | X0_54 != sK4
% 1.78/1.08      | sK8 != sK7 ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_3995]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_4381,plain,
% 1.78/1.08      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 1.78/1.08      | r1_tmap_1(sK3,sK2,sK4,sK8)
% 1.78/1.08      | sK8 != sK7
% 1.78/1.08      | sK4 != sK4 ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_4379]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_2699,plain,
% 1.78/1.08      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 1.78/1.08      theory(equality) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3737,plain,
% 1.78/1.08      ( X0_54 != X1_54 | X0_54 = sK7 | sK7 != X1_54 ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_2699]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3906,plain,
% 1.78/1.08      ( X0_54 = sK7 | X0_54 != sK8 | sK7 != sK8 ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_3737]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3954,plain,
% 1.78/1.08      ( sK7 != sK8 | sK8 = sK7 | sK8 != sK8 ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_3906]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_0,plain,
% 1.78/1.08      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 1.78/1.08      inference(cnf_transformation,[],[f36]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_2692,plain,
% 1.78/1.08      ( ~ r1_tarski(X0_54,X1_54)
% 1.78/1.08      | ~ r1_tarski(X2_54,X0_54)
% 1.78/1.08      | r1_tarski(X2_54,X1_54) ),
% 1.78/1.08      inference(subtyping,[status(esa)],[c_0]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3639,plain,
% 1.78/1.08      ( r1_tarski(X0_54,u1_struct_0(sK5))
% 1.78/1.08      | ~ r1_tarski(X0_54,sK6)
% 1.78/1.08      | ~ r1_tarski(sK6,u1_struct_0(sK5)) ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_2692]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3897,plain,
% 1.78/1.08      ( r1_tarski(sK1(sK3,sK6,sK7),u1_struct_0(sK5))
% 1.78/1.08      | ~ r1_tarski(sK1(sK3,sK6,sK7),sK6)
% 1.78/1.08      | ~ r1_tarski(sK6,u1_struct_0(sK5)) ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_3639]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_2698,plain,( X0_54 = X0_54 ),theory(equality) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3835,plain,
% 1.78/1.08      ( k2_tmap_1(sK3,sK2,sK4,sK5) = k2_tmap_1(sK3,sK2,sK4,sK5) ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_2698]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3685,plain,
% 1.78/1.08      ( r1_tmap_1(sK5,sK2,X0_54,X1_54)
% 1.78/1.08      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 1.78/1.08      | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 1.78/1.08      | X1_54 != sK8 ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_2707]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3769,plain,
% 1.78/1.08      ( r1_tmap_1(sK5,sK2,X0_54,sK7)
% 1.78/1.08      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 1.78/1.08      | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 1.78/1.08      | sK7 != sK8 ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_3685]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3834,plain,
% 1.78/1.08      ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 1.78/1.08      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 1.78/1.08      | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
% 1.78/1.08      | sK7 != sK8 ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_3769]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3819,plain,
% 1.78/1.08      ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_2698]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_2702,plain,
% 1.78/1.08      ( ~ m1_subset_1(X0_54,X1_54)
% 1.78/1.08      | m1_subset_1(X2_54,X3_54)
% 1.78/1.08      | X2_54 != X0_54
% 1.78/1.08      | X3_54 != X1_54 ),
% 1.78/1.08      theory(equality) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3660,plain,
% 1.78/1.08      ( m1_subset_1(X0_54,X1_54)
% 1.78/1.08      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 1.78/1.08      | X1_54 != u1_struct_0(sK5)
% 1.78/1.08      | X0_54 != sK8 ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_2702]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3718,plain,
% 1.78/1.08      ( m1_subset_1(sK7,X0_54)
% 1.78/1.08      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 1.78/1.08      | X0_54 != u1_struct_0(sK5)
% 1.78/1.08      | sK7 != sK8 ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_3660]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3818,plain,
% 1.78/1.08      ( m1_subset_1(sK7,u1_struct_0(sK5))
% 1.78/1.08      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 1.78/1.08      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 1.78/1.08      | sK7 != sK8 ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_3718]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3724,plain,
% 1.78/1.08      ( sK8 = sK8 ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_2698]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_23,negated_conjecture,
% 1.78/1.08      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 1.78/1.08      inference(cnf_transformation,[],[f54]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_10,plain,
% 1.78/1.08      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.78/1.08      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.78/1.08      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.78/1.08      | ~ m1_connsp_2(X5,X0,X3)
% 1.78/1.08      | ~ m1_pre_topc(X4,X0)
% 1.78/1.08      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.78/1.08      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.78/1.08      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.78/1.08      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.78/1.08      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.78/1.08      | ~ v1_funct_1(X2)
% 1.78/1.08      | v2_struct_0(X1)
% 1.78/1.08      | v2_struct_0(X0)
% 1.78/1.08      | v2_struct_0(X4)
% 1.78/1.08      | ~ v2_pre_topc(X1)
% 1.78/1.08      | ~ v2_pre_topc(X0)
% 1.78/1.08      | ~ l1_pre_topc(X1)
% 1.78/1.08      | ~ l1_pre_topc(X0) ),
% 1.78/1.08      inference(cnf_transformation,[],[f69]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_8,plain,
% 1.78/1.08      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.78/1.08      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.78/1.08      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.78/1.08      | ~ m1_pre_topc(X4,X0)
% 1.78/1.08      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.78/1.08      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.78/1.08      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.78/1.08      | ~ v1_funct_1(X2)
% 1.78/1.08      | v2_struct_0(X1)
% 1.78/1.08      | v2_struct_0(X0)
% 1.78/1.08      | v2_struct_0(X4)
% 1.78/1.08      | ~ v2_pre_topc(X1)
% 1.78/1.08      | ~ v2_pre_topc(X0)
% 1.78/1.08      | ~ l1_pre_topc(X1)
% 1.78/1.08      | ~ l1_pre_topc(X0) ),
% 1.78/1.08      inference(cnf_transformation,[],[f67]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_161,plain,
% 1.78/1.08      ( ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.78/1.08      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.78/1.08      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.78/1.08      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.78/1.08      | ~ r1_tmap_1(X0,X1,X2,X3)
% 1.78/1.08      | ~ m1_pre_topc(X4,X0)
% 1.78/1.08      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.78/1.08      | ~ v1_funct_1(X2)
% 1.78/1.08      | v2_struct_0(X1)
% 1.78/1.08      | v2_struct_0(X0)
% 1.78/1.08      | v2_struct_0(X4)
% 1.78/1.08      | ~ v2_pre_topc(X1)
% 1.78/1.08      | ~ v2_pre_topc(X0)
% 1.78/1.08      | ~ l1_pre_topc(X1)
% 1.78/1.08      | ~ l1_pre_topc(X0) ),
% 1.78/1.08      inference(global_propositional_subsumption,
% 1.78/1.08                [status(thm)],
% 1.78/1.08                [c_10,c_8]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_162,plain,
% 1.78/1.08      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.78/1.08      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.78/1.08      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.78/1.08      | ~ m1_pre_topc(X4,X0)
% 1.78/1.08      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.78/1.08      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.78/1.08      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.78/1.08      | ~ v1_funct_1(X2)
% 1.78/1.08      | v2_struct_0(X0)
% 1.78/1.08      | v2_struct_0(X1)
% 1.78/1.08      | v2_struct_0(X4)
% 1.78/1.08      | ~ v2_pre_topc(X0)
% 1.78/1.08      | ~ v2_pre_topc(X1)
% 1.78/1.08      | ~ l1_pre_topc(X0)
% 1.78/1.08      | ~ l1_pre_topc(X1) ),
% 1.78/1.08      inference(renaming,[status(thm)],[c_161]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_20,negated_conjecture,
% 1.78/1.08      ( m1_pre_topc(sK5,sK3) ),
% 1.78/1.08      inference(cnf_transformation,[],[f57]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_393,plain,
% 1.78/1.08      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.78/1.08      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.78/1.08      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.78/1.08      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.78/1.08      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.78/1.08      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.78/1.08      | ~ v1_funct_1(X2)
% 1.78/1.08      | v2_struct_0(X0)
% 1.78/1.08      | v2_struct_0(X1)
% 1.78/1.08      | v2_struct_0(X4)
% 1.78/1.08      | ~ v2_pre_topc(X0)
% 1.78/1.08      | ~ v2_pre_topc(X1)
% 1.78/1.08      | ~ l1_pre_topc(X0)
% 1.78/1.08      | ~ l1_pre_topc(X1)
% 1.78/1.08      | sK3 != X0
% 1.78/1.08      | sK5 != X4 ),
% 1.78/1.08      inference(resolution_lifted,[status(thm)],[c_162,c_20]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_394,plain,
% 1.78/1.08      ( ~ r1_tmap_1(sK3,X0,X1,X2)
% 1.78/1.08      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 1.78/1.08      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 1.78/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.08      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.78/1.08      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.78/1.08      | ~ v1_funct_1(X1)
% 1.78/1.08      | v2_struct_0(X0)
% 1.78/1.08      | v2_struct_0(sK3)
% 1.78/1.08      | v2_struct_0(sK5)
% 1.78/1.08      | ~ v2_pre_topc(X0)
% 1.78/1.08      | ~ v2_pre_topc(sK3)
% 1.78/1.08      | ~ l1_pre_topc(X0)
% 1.78/1.08      | ~ l1_pre_topc(sK3) ),
% 1.78/1.08      inference(unflattening,[status(thm)],[c_393]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_27,negated_conjecture,
% 1.78/1.08      ( ~ v2_struct_0(sK3) ),
% 1.78/1.08      inference(cnf_transformation,[],[f50]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_26,negated_conjecture,
% 1.78/1.08      ( v2_pre_topc(sK3) ),
% 1.78/1.08      inference(cnf_transformation,[],[f51]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_25,negated_conjecture,
% 1.78/1.08      ( l1_pre_topc(sK3) ),
% 1.78/1.08      inference(cnf_transformation,[],[f52]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_21,negated_conjecture,
% 1.78/1.08      ( ~ v2_struct_0(sK5) ),
% 1.78/1.08      inference(cnf_transformation,[],[f56]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_398,plain,
% 1.78/1.08      ( ~ l1_pre_topc(X0)
% 1.78/1.08      | ~ r1_tmap_1(sK3,X0,X1,X2)
% 1.78/1.08      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 1.78/1.08      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 1.78/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.08      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.78/1.08      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.78/1.08      | ~ v1_funct_1(X1)
% 1.78/1.08      | v2_struct_0(X0)
% 1.78/1.08      | ~ v2_pre_topc(X0) ),
% 1.78/1.08      inference(global_propositional_subsumption,
% 1.78/1.08                [status(thm)],
% 1.78/1.08                [c_394,c_27,c_26,c_25,c_21]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_399,plain,
% 1.78/1.08      ( ~ r1_tmap_1(sK3,X0,X1,X2)
% 1.78/1.08      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 1.78/1.08      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 1.78/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.08      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.78/1.08      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.78/1.08      | ~ v1_funct_1(X1)
% 1.78/1.08      | v2_struct_0(X0)
% 1.78/1.08      | ~ v2_pre_topc(X0)
% 1.78/1.08      | ~ l1_pre_topc(X0) ),
% 1.78/1.08      inference(renaming,[status(thm)],[c_398]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_553,plain,
% 1.78/1.08      ( ~ r1_tmap_1(sK3,X0,X1,X2)
% 1.78/1.08      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 1.78/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.08      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.78/1.08      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.78/1.08      | ~ v1_funct_1(X1)
% 1.78/1.08      | v2_struct_0(X0)
% 1.78/1.08      | ~ v2_pre_topc(X0)
% 1.78/1.08      | ~ l1_pre_topc(X0)
% 1.78/1.08      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.78/1.08      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.78/1.08      | sK4 != X1 ),
% 1.78/1.08      inference(resolution_lifted,[status(thm)],[c_23,c_399]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_554,plain,
% 1.78/1.08      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 1.78/1.08      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.78/1.08      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.78/1.08      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.78/1.08      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.08      | ~ v1_funct_1(sK4)
% 1.78/1.08      | v2_struct_0(X0)
% 1.78/1.08      | ~ v2_pre_topc(X0)
% 1.78/1.08      | ~ l1_pre_topc(X0)
% 1.78/1.08      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.78/1.08      inference(unflattening,[status(thm)],[c_553]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_24,negated_conjecture,
% 1.78/1.08      ( v1_funct_1(sK4) ),
% 1.78/1.08      inference(cnf_transformation,[],[f53]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_558,plain,
% 1.78/1.08      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.08      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.78/1.08      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.78/1.08      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.78/1.08      | ~ r1_tmap_1(sK3,X0,sK4,X1)
% 1.78/1.08      | v2_struct_0(X0)
% 1.78/1.08      | ~ v2_pre_topc(X0)
% 1.78/1.08      | ~ l1_pre_topc(X0)
% 1.78/1.08      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.78/1.08      inference(global_propositional_subsumption,
% 1.78/1.08                [status(thm)],
% 1.78/1.08                [c_554,c_24]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_559,plain,
% 1.78/1.08      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 1.78/1.08      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.78/1.08      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.78/1.08      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.78/1.08      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.08      | v2_struct_0(X0)
% 1.78/1.08      | ~ v2_pre_topc(X0)
% 1.78/1.08      | ~ l1_pre_topc(X0)
% 1.78/1.08      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.78/1.08      inference(renaming,[status(thm)],[c_558]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_28,negated_conjecture,
% 1.78/1.08      ( l1_pre_topc(sK2) ),
% 1.78/1.08      inference(cnf_transformation,[],[f49]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_1236,plain,
% 1.78/1.08      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 1.78/1.08      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.78/1.08      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.78/1.08      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.78/1.08      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.08      | v2_struct_0(X0)
% 1.78/1.08      | ~ v2_pre_topc(X0)
% 1.78/1.08      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.78/1.08      | sK2 != X0 ),
% 1.78/1.08      inference(resolution_lifted,[status(thm)],[c_559,c_28]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_1237,plain,
% 1.78/1.08      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 1.78/1.08      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.78/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.78/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.78/1.08      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 1.78/1.08      | v2_struct_0(sK2)
% 1.78/1.08      | ~ v2_pre_topc(sK2)
% 1.78/1.08      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.78/1.08      inference(unflattening,[status(thm)],[c_1236]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_30,negated_conjecture,
% 1.78/1.08      ( ~ v2_struct_0(sK2) ),
% 1.78/1.08      inference(cnf_transformation,[],[f47]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_29,negated_conjecture,
% 1.78/1.08      ( v2_pre_topc(sK2) ),
% 1.78/1.08      inference(cnf_transformation,[],[f48]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_22,negated_conjecture,
% 1.78/1.08      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 1.78/1.08      inference(cnf_transformation,[],[f55]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_1241,plain,
% 1.78/1.08      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.78/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.78/1.08      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.78/1.08      | ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 1.78/1.08      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.78/1.08      inference(global_propositional_subsumption,
% 1.78/1.08                [status(thm)],
% 1.78/1.08                [c_1237,c_30,c_29,c_22]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_1242,plain,
% 1.78/1.08      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 1.78/1.08      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.78/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.78/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.78/1.08      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.78/1.08      inference(renaming,[status(thm)],[c_1241]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_2033,plain,
% 1.78/1.08      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 1.78/1.08      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.78/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.78/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 1.78/1.08      inference(equality_resolution_simp,[status(thm)],[c_1242]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_2668,plain,
% 1.78/1.08      ( ~ r1_tmap_1(sK3,sK2,sK4,X0_54)
% 1.78/1.08      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
% 1.78/1.08      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 1.78/1.08      | ~ m1_subset_1(X0_54,u1_struct_0(sK5)) ),
% 1.78/1.08      inference(subtyping,[status(esa)],[c_2033]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3631,plain,
% 1.78/1.08      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 1.78/1.08      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 1.78/1.08      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 1.78/1.08      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_2668]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_11,negated_conjecture,
% 1.78/1.08      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 1.78/1.08      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 1.78/1.08      inference(cnf_transformation,[],[f66]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_2691,negated_conjecture,
% 1.78/1.08      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 1.78/1.08      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 1.78/1.08      inference(subtyping,[status(esa)],[c_11]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3339,plain,
% 1.78/1.08      ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
% 1.78/1.08      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) != iProver_top ),
% 1.78/1.08      inference(predicate_to_equality,[status(thm)],[c_2691]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_13,negated_conjecture,
% 1.78/1.08      ( sK7 = sK8 ),
% 1.78/1.08      inference(cnf_transformation,[],[f64]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_2689,negated_conjecture,
% 1.78/1.08      ( sK7 = sK8 ),
% 1.78/1.08      inference(subtyping,[status(esa)],[c_13]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3393,plain,
% 1.78/1.08      ( r1_tmap_1(sK3,sK2,sK4,sK8) != iProver_top
% 1.78/1.08      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) != iProver_top ),
% 1.78/1.08      inference(light_normalisation,[status(thm)],[c_3339,c_2689]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3572,plain,
% 1.78/1.08      ( ~ r1_tmap_1(sK3,sK2,sK4,sK8)
% 1.78/1.08      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 1.78/1.08      inference(predicate_to_equality_rev,[status(thm)],[c_3393]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_12,negated_conjecture,
% 1.78/1.08      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 1.78/1.08      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 1.78/1.08      inference(cnf_transformation,[],[f65]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_2690,negated_conjecture,
% 1.78/1.08      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 1.78/1.08      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 1.78/1.08      inference(subtyping,[status(esa)],[c_12]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3340,plain,
% 1.78/1.08      ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
% 1.78/1.08      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) = iProver_top ),
% 1.78/1.08      inference(predicate_to_equality,[status(thm)],[c_2690]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3388,plain,
% 1.78/1.08      ( r1_tmap_1(sK3,sK2,sK4,sK8) = iProver_top
% 1.78/1.08      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) = iProver_top ),
% 1.78/1.08      inference(light_normalisation,[status(thm)],[c_3340,c_2689]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_3557,plain,
% 1.78/1.08      ( r1_tmap_1(sK3,sK2,sK4,sK8)
% 1.78/1.08      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 1.78/1.08      inference(predicate_to_equality_rev,[status(thm)],[c_3388]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_2719,plain,
% 1.78/1.08      ( sK4 = sK4 ),
% 1.78/1.08      inference(instantiation,[status(thm)],[c_2698]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_7,plain,
% 1.78/1.08      ( ~ r2_hidden(X0,X1)
% 1.78/1.08      | ~ v3_pre_topc(X1,X2)
% 1.78/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.78/1.08      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 1.78/1.08      | m1_subset_1(sK1(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 1.78/1.08      | v2_struct_0(X2)
% 1.78/1.08      | ~ v2_pre_topc(X2)
% 1.78/1.08      | ~ l1_pre_topc(X2) ),
% 1.78/1.08      inference(cnf_transformation,[],[f38]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_1326,plain,
% 1.78/1.08      ( ~ r2_hidden(X0,X1)
% 1.78/1.08      | ~ v3_pre_topc(X1,X2)
% 1.78/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.78/1.08      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 1.78/1.08      | m1_subset_1(sK1(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 1.78/1.08      | v2_struct_0(X2)
% 1.78/1.08      | ~ v2_pre_topc(X2)
% 1.78/1.08      | sK3 != X2 ),
% 1.78/1.08      inference(resolution_lifted,[status(thm)],[c_7,c_25]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_1327,plain,
% 1.78/1.08      ( ~ r2_hidden(X0,X1)
% 1.78/1.08      | ~ v3_pre_topc(X1,sK3)
% 1.78/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.78/1.08      | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.08      | v2_struct_0(sK3)
% 1.78/1.08      | ~ v2_pre_topc(sK3) ),
% 1.78/1.08      inference(unflattening,[status(thm)],[c_1326]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_1331,plain,
% 1.78/1.08      ( ~ r2_hidden(X0,X1)
% 1.78/1.08      | ~ v3_pre_topc(X1,sK3)
% 1.78/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.78/1.08      | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.78/1.08      inference(global_propositional_subsumption,
% 1.78/1.08                [status(thm)],
% 1.78/1.08                [c_1327,c_27,c_26]) ).
% 1.78/1.08  
% 1.78/1.08  cnf(c_6,plain,
% 1.78/1.08      ( m1_connsp_2(sK1(X0,X1,X2),X0,X2)
% 1.78/1.08      | ~ r2_hidden(X2,X1)
% 1.78/1.08      | ~ v3_pre_topc(X1,X0)
% 1.78/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.78/1.08      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.78/1.09      | v2_struct_0(X0)
% 1.78/1.09      | ~ v2_pre_topc(X0)
% 1.78/1.09      | ~ l1_pre_topc(X0) ),
% 1.78/1.09      inference(cnf_transformation,[],[f39]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_9,plain,
% 1.78/1.09      ( r1_tmap_1(X0,X1,X2,X3)
% 1.78/1.09      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.78/1.09      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.78/1.09      | ~ m1_connsp_2(X5,X0,X3)
% 1.78/1.09      | ~ m1_pre_topc(X4,X0)
% 1.78/1.09      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.78/1.09      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.78/1.09      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.78/1.09      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.78/1.09      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.78/1.09      | ~ v1_funct_1(X2)
% 1.78/1.09      | v2_struct_0(X1)
% 1.78/1.09      | v2_struct_0(X0)
% 1.78/1.09      | v2_struct_0(X4)
% 1.78/1.09      | ~ v2_pre_topc(X1)
% 1.78/1.09      | ~ v2_pre_topc(X0)
% 1.78/1.09      | ~ l1_pre_topc(X1)
% 1.78/1.09      | ~ l1_pre_topc(X0) ),
% 1.78/1.09      inference(cnf_transformation,[],[f68]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_435,plain,
% 1.78/1.09      ( r1_tmap_1(X0,X1,X2,X3)
% 1.78/1.09      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.78/1.09      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.78/1.09      | ~ m1_connsp_2(X5,X0,X3)
% 1.78/1.09      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.78/1.09      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.78/1.09      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.78/1.09      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.78/1.09      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.78/1.09      | ~ v1_funct_1(X2)
% 1.78/1.09      | v2_struct_0(X0)
% 1.78/1.09      | v2_struct_0(X1)
% 1.78/1.09      | v2_struct_0(X4)
% 1.78/1.09      | ~ v2_pre_topc(X0)
% 1.78/1.09      | ~ v2_pre_topc(X1)
% 1.78/1.09      | ~ l1_pre_topc(X0)
% 1.78/1.09      | ~ l1_pre_topc(X1)
% 1.78/1.09      | sK3 != X0
% 1.78/1.09      | sK5 != X4 ),
% 1.78/1.09      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_436,plain,
% 1.78/1.09      ( r1_tmap_1(sK3,X0,X1,X2)
% 1.78/1.09      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 1.78/1.09      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 1.78/1.09      | ~ m1_connsp_2(X3,sK3,X2)
% 1.78/1.09      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.09      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.78/1.09      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 1.78/1.09      | ~ v1_funct_1(X1)
% 1.78/1.09      | v2_struct_0(X0)
% 1.78/1.09      | v2_struct_0(sK3)
% 1.78/1.09      | v2_struct_0(sK5)
% 1.78/1.09      | ~ v2_pre_topc(X0)
% 1.78/1.09      | ~ v2_pre_topc(sK3)
% 1.78/1.09      | ~ l1_pre_topc(X0)
% 1.78/1.09      | ~ l1_pre_topc(sK3) ),
% 1.78/1.09      inference(unflattening,[status(thm)],[c_435]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_440,plain,
% 1.78/1.09      ( ~ l1_pre_topc(X0)
% 1.78/1.09      | r1_tmap_1(sK3,X0,X1,X2)
% 1.78/1.09      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 1.78/1.09      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 1.78/1.09      | ~ m1_connsp_2(X3,sK3,X2)
% 1.78/1.09      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.09      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.78/1.09      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 1.78/1.09      | ~ v1_funct_1(X1)
% 1.78/1.09      | v2_struct_0(X0)
% 1.78/1.09      | ~ v2_pre_topc(X0) ),
% 1.78/1.09      inference(global_propositional_subsumption,
% 1.78/1.09                [status(thm)],
% 1.78/1.09                [c_436,c_27,c_26,c_25,c_21]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_441,plain,
% 1.78/1.09      ( r1_tmap_1(sK3,X0,X1,X2)
% 1.78/1.09      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 1.78/1.09      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 1.78/1.09      | ~ m1_connsp_2(X3,sK3,X2)
% 1.78/1.09      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.09      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.78/1.09      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 1.78/1.09      | ~ v1_funct_1(X1)
% 1.78/1.09      | v2_struct_0(X0)
% 1.78/1.09      | ~ v2_pre_topc(X0)
% 1.78/1.09      | ~ l1_pre_topc(X0) ),
% 1.78/1.09      inference(renaming,[status(thm)],[c_440]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_505,plain,
% 1.78/1.09      ( r1_tmap_1(sK3,X0,X1,X2)
% 1.78/1.09      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 1.78/1.09      | ~ m1_connsp_2(X3,sK3,X2)
% 1.78/1.09      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.09      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.78/1.09      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 1.78/1.09      | ~ v1_funct_1(X1)
% 1.78/1.09      | v2_struct_0(X0)
% 1.78/1.09      | ~ v2_pre_topc(X0)
% 1.78/1.09      | ~ l1_pre_topc(X0)
% 1.78/1.09      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.78/1.09      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.78/1.09      | sK4 != X1 ),
% 1.78/1.09      inference(resolution_lifted,[status(thm)],[c_23,c_441]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_506,plain,
% 1.78/1.09      ( r1_tmap_1(sK3,X0,sK4,X1)
% 1.78/1.09      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.78/1.09      | ~ m1_connsp_2(X2,sK3,X1)
% 1.78/1.09      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.78/1.09      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.09      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 1.78/1.09      | ~ v1_funct_1(sK4)
% 1.78/1.09      | v2_struct_0(X0)
% 1.78/1.09      | ~ v2_pre_topc(X0)
% 1.78/1.09      | ~ l1_pre_topc(X0)
% 1.78/1.09      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.78/1.09      inference(unflattening,[status(thm)],[c_505]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_510,plain,
% 1.78/1.09      ( ~ r1_tarski(X2,u1_struct_0(sK5))
% 1.78/1.09      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.09      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.78/1.09      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_connsp_2(X2,sK3,X1)
% 1.78/1.09      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.78/1.09      | r1_tmap_1(sK3,X0,sK4,X1)
% 1.78/1.09      | v2_struct_0(X0)
% 1.78/1.09      | ~ v2_pre_topc(X0)
% 1.78/1.09      | ~ l1_pre_topc(X0)
% 1.78/1.09      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.78/1.09      inference(global_propositional_subsumption,
% 1.78/1.09                [status(thm)],
% 1.78/1.09                [c_506,c_24]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_511,plain,
% 1.78/1.09      ( r1_tmap_1(sK3,X0,sK4,X1)
% 1.78/1.09      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.78/1.09      | ~ m1_connsp_2(X2,sK3,X1)
% 1.78/1.09      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.78/1.09      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.09      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 1.78/1.09      | v2_struct_0(X0)
% 1.78/1.09      | ~ v2_pre_topc(X0)
% 1.78/1.09      | ~ l1_pre_topc(X0)
% 1.78/1.09      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.78/1.09      inference(renaming,[status(thm)],[c_510]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_641,plain,
% 1.78/1.09      ( r1_tmap_1(sK3,X0,sK4,X1)
% 1.78/1.09      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.78/1.09      | ~ r2_hidden(X2,X3)
% 1.78/1.09      | ~ v3_pre_topc(X3,X4)
% 1.78/1.09      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
% 1.78/1.09      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(X2,u1_struct_0(X4))
% 1.78/1.09      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.78/1.09      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.09      | ~ r1_tarski(X5,u1_struct_0(sK5))
% 1.78/1.09      | v2_struct_0(X4)
% 1.78/1.09      | v2_struct_0(X0)
% 1.78/1.09      | ~ v2_pre_topc(X4)
% 1.78/1.09      | ~ v2_pre_topc(X0)
% 1.78/1.09      | ~ l1_pre_topc(X4)
% 1.78/1.09      | ~ l1_pre_topc(X0)
% 1.78/1.09      | X1 != X2
% 1.78/1.09      | sK1(X4,X3,X2) != X5
% 1.78/1.09      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.78/1.09      | sK3 != X4 ),
% 1.78/1.09      inference(resolution_lifted,[status(thm)],[c_6,c_511]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_642,plain,
% 1.78/1.09      ( r1_tmap_1(sK3,X0,sK4,X1)
% 1.78/1.09      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.78/1.09      | ~ r2_hidden(X1,X2)
% 1.78/1.09      | ~ v3_pre_topc(X2,sK3)
% 1.78/1.09      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.78/1.09      | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.09      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 1.78/1.09      | v2_struct_0(X0)
% 1.78/1.09      | v2_struct_0(sK3)
% 1.78/1.09      | ~ v2_pre_topc(X0)
% 1.78/1.09      | ~ v2_pre_topc(sK3)
% 1.78/1.09      | ~ l1_pre_topc(X0)
% 1.78/1.09      | ~ l1_pre_topc(sK3)
% 1.78/1.09      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.78/1.09      inference(unflattening,[status(thm)],[c_641]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_646,plain,
% 1.78/1.09      ( ~ l1_pre_topc(X0)
% 1.78/1.09      | v2_struct_0(X0)
% 1.78/1.09      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 1.78/1.09      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.09      | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.78/1.09      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ v3_pre_topc(X2,sK3)
% 1.78/1.09      | ~ r2_hidden(X1,X2)
% 1.78/1.09      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.78/1.09      | r1_tmap_1(sK3,X0,sK4,X1)
% 1.78/1.09      | ~ v2_pre_topc(X0)
% 1.78/1.09      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.78/1.09      inference(global_propositional_subsumption,
% 1.78/1.09                [status(thm)],
% 1.78/1.09                [c_642,c_27,c_26,c_25]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_647,plain,
% 1.78/1.09      ( r1_tmap_1(sK3,X0,sK4,X1)
% 1.78/1.09      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.78/1.09      | ~ r2_hidden(X1,X2)
% 1.78/1.09      | ~ v3_pre_topc(X2,sK3)
% 1.78/1.09      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.78/1.09      | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.09      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 1.78/1.09      | v2_struct_0(X0)
% 1.78/1.09      | ~ v2_pre_topc(X0)
% 1.78/1.09      | ~ l1_pre_topc(X0)
% 1.78/1.09      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.78/1.09      inference(renaming,[status(thm)],[c_646]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_1168,plain,
% 1.78/1.09      ( r1_tmap_1(sK3,X0,sK4,X1)
% 1.78/1.09      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.78/1.09      | ~ r2_hidden(X1,X2)
% 1.78/1.09      | ~ v3_pre_topc(X2,sK3)
% 1.78/1.09      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.78/1.09      | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.78/1.09      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 1.78/1.09      | v2_struct_0(X0)
% 1.78/1.09      | ~ v2_pre_topc(X0)
% 1.78/1.09      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.78/1.09      | sK2 != X0 ),
% 1.78/1.09      inference(resolution_lifted,[status(thm)],[c_647,c_28]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_1169,plain,
% 1.78/1.09      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 1.78/1.09      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.78/1.09      | ~ r2_hidden(X0,X1)
% 1.78/1.09      | ~ v3_pre_topc(X1,sK3)
% 1.78/1.09      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.78/1.09      | ~ m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 1.78/1.09      | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
% 1.78/1.09      | v2_struct_0(sK2)
% 1.78/1.09      | ~ v2_pre_topc(sK2)
% 1.78/1.09      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.78/1.09      inference(unflattening,[status(thm)],[c_1168]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_1173,plain,
% 1.78/1.09      ( ~ m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.78/1.09      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ v3_pre_topc(X1,sK3)
% 1.78/1.09      | ~ r2_hidden(X0,X1)
% 1.78/1.09      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.78/1.09      | r1_tmap_1(sK3,sK2,sK4,X0)
% 1.78/1.09      | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
% 1.78/1.09      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.78/1.09      inference(global_propositional_subsumption,
% 1.78/1.09                [status(thm)],
% 1.78/1.09                [c_1169,c_30,c_29,c_22]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_1174,plain,
% 1.78/1.09      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 1.78/1.09      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.78/1.09      | ~ r2_hidden(X0,X1)
% 1.78/1.09      | ~ v3_pre_topc(X1,sK3)
% 1.78/1.09      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.78/1.09      | ~ m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
% 1.78/1.09      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.78/1.09      inference(renaming,[status(thm)],[c_1173]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_1353,plain,
% 1.78/1.09      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 1.78/1.09      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.78/1.09      | ~ r2_hidden(X0,X1)
% 1.78/1.09      | ~ v3_pre_topc(X1,sK3)
% 1.78/1.09      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.78/1.09      | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
% 1.78/1.09      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.78/1.09      inference(backward_subsumption_resolution,
% 1.78/1.09                [status(thm)],
% 1.78/1.09                [c_1331,c_1174]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_15,negated_conjecture,
% 1.78/1.09      ( r2_hidden(sK7,sK6) ),
% 1.78/1.09      inference(cnf_transformation,[],[f62]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_1573,plain,
% 1.78/1.09      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 1.78/1.09      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.78/1.09      | ~ v3_pre_topc(X1,sK3)
% 1.78/1.09      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.78/1.09      | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
% 1.78/1.09      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.78/1.09      | sK6 != X1
% 1.78/1.09      | sK7 != X0 ),
% 1.78/1.09      inference(resolution_lifted,[status(thm)],[c_1353,c_15]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_1574,plain,
% 1.78/1.09      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 1.78/1.09      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 1.78/1.09      | ~ v3_pre_topc(sK6,sK3)
% 1.78/1.09      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 1.78/1.09      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 1.78/1.09      | ~ r1_tarski(sK1(sK3,sK6,sK7),u1_struct_0(sK5)) ),
% 1.78/1.09      inference(unflattening,[status(thm)],[c_1573]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_19,negated_conjecture,
% 1.78/1.09      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.78/1.09      inference(cnf_transformation,[],[f58]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_18,negated_conjecture,
% 1.78/1.09      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 1.78/1.09      inference(cnf_transformation,[],[f59]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_16,negated_conjecture,
% 1.78/1.09      ( v3_pre_topc(sK6,sK3) ),
% 1.78/1.09      inference(cnf_transformation,[],[f61]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_1576,plain,
% 1.78/1.09      ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 1.78/1.09      | r1_tmap_1(sK3,sK2,sK4,sK7)
% 1.78/1.09      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 1.78/1.09      | ~ r1_tarski(sK1(sK3,sK6,sK7),u1_struct_0(sK5)) ),
% 1.78/1.09      inference(global_propositional_subsumption,
% 1.78/1.09                [status(thm)],
% 1.78/1.09                [c_1574,c_19,c_18,c_16]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_1577,plain,
% 1.78/1.09      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 1.78/1.09      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 1.78/1.09      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 1.78/1.09      | ~ r1_tarski(sK1(sK3,sK6,sK7),u1_struct_0(sK5)) ),
% 1.78/1.09      inference(renaming,[status(thm)],[c_1576]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_5,plain,
% 1.78/1.09      ( ~ r2_hidden(X0,X1)
% 1.78/1.09      | ~ v3_pre_topc(X1,X2)
% 1.78/1.09      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.78/1.09      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 1.78/1.09      | r1_tarski(sK1(X2,X1,X0),X1)
% 1.78/1.09      | v2_struct_0(X2)
% 1.78/1.09      | ~ v2_pre_topc(X2)
% 1.78/1.09      | ~ l1_pre_topc(X2) ),
% 1.78/1.09      inference(cnf_transformation,[],[f40]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_915,plain,
% 1.78/1.09      ( ~ v3_pre_topc(X0,X1)
% 1.78/1.09      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/1.09      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.78/1.09      | r1_tarski(sK1(X1,X0,X2),X0)
% 1.78/1.09      | v2_struct_0(X1)
% 1.78/1.09      | ~ v2_pre_topc(X1)
% 1.78/1.09      | ~ l1_pre_topc(X1)
% 1.78/1.09      | sK6 != X0
% 1.78/1.09      | sK7 != X2 ),
% 1.78/1.09      inference(resolution_lifted,[status(thm)],[c_5,c_15]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_916,plain,
% 1.78/1.09      ( ~ v3_pre_topc(sK6,X0)
% 1.78/1.09      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.78/1.09      | ~ m1_subset_1(sK7,u1_struct_0(X0))
% 1.78/1.09      | r1_tarski(sK1(X0,sK6,sK7),sK6)
% 1.78/1.09      | v2_struct_0(X0)
% 1.78/1.09      | ~ v2_pre_topc(X0)
% 1.78/1.09      | ~ l1_pre_topc(X0) ),
% 1.78/1.09      inference(unflattening,[status(thm)],[c_915]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_918,plain,
% 1.78/1.09      ( ~ v3_pre_topc(sK6,sK3)
% 1.78/1.09      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.78/1.09      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 1.78/1.09      | r1_tarski(sK1(sK3,sK6,sK7),sK6)
% 1.78/1.09      | v2_struct_0(sK3)
% 1.78/1.09      | ~ v2_pre_topc(sK3)
% 1.78/1.09      | ~ l1_pre_topc(sK3) ),
% 1.78/1.09      inference(instantiation,[status(thm)],[c_916]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_14,negated_conjecture,
% 1.78/1.09      ( r1_tarski(sK6,u1_struct_0(sK5)) ),
% 1.78/1.09      inference(cnf_transformation,[],[f63]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(c_17,negated_conjecture,
% 1.78/1.09      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 1.78/1.09      inference(cnf_transformation,[],[f60]) ).
% 1.78/1.09  
% 1.78/1.09  cnf(contradiction,plain,
% 1.78/1.09      ( $false ),
% 1.78/1.09      inference(minisat,
% 1.78/1.09                [status(thm)],
% 1.78/1.09                [c_4564,c_4381,c_3954,c_3897,c_3835,c_3834,c_3819,c_3818,
% 1.78/1.09                 c_3724,c_3631,c_3572,c_3557,c_2689,c_2719,c_1577,c_918,
% 1.78/1.09                 c_12,c_14,c_16,c_17,c_18,c_19,c_25,c_26,c_27]) ).
% 1.78/1.09  
% 1.78/1.09  
% 1.78/1.09  % SZS output end CNFRefutation for theBenchmark.p
% 1.78/1.09  
% 1.78/1.09  ------                               Statistics
% 1.78/1.09  
% 1.78/1.09  ------ General
% 1.78/1.09  
% 1.78/1.09  abstr_ref_over_cycles:                  0
% 1.78/1.09  abstr_ref_under_cycles:                 0
% 1.78/1.09  gc_basic_clause_elim:                   0
% 1.78/1.09  forced_gc_time:                         0
% 1.78/1.09  parsing_time:                           0.013
% 1.78/1.09  unif_index_cands_time:                  0.
% 1.78/1.09  unif_index_add_time:                    0.
% 1.78/1.09  orderings_time:                         0.
% 1.78/1.09  out_proof_time:                         0.012
% 1.78/1.09  total_time:                             0.233
% 1.78/1.09  num_of_symbols:                         60
% 1.78/1.09  num_of_terms:                           3357
% 1.78/1.09  
% 1.78/1.09  ------ Preprocessing
% 1.78/1.09  
% 1.78/1.09  num_of_splits:                          2
% 1.78/1.09  num_of_split_atoms:                     2
% 1.78/1.09  num_of_reused_defs:                     0
% 1.78/1.09  num_eq_ax_congr_red:                    19
% 1.78/1.09  num_of_sem_filtered_clauses:            1
% 1.78/1.09  num_of_subtypes:                        2
% 1.78/1.09  monotx_restored_types:                  0
% 1.78/1.09  sat_num_of_epr_types:                   0
% 1.78/1.09  sat_num_of_non_cyclic_types:            0
% 1.78/1.09  sat_guarded_non_collapsed_types:        0
% 1.78/1.09  num_pure_diseq_elim:                    0
% 1.78/1.09  simp_replaced_by:                       0
% 1.78/1.09  res_preprocessed:                       133
% 1.78/1.09  prep_upred:                             0
% 1.78/1.09  prep_unflattend:                        129
% 1.78/1.09  smt_new_axioms:                         0
% 1.78/1.09  pred_elim_cands:                        5
% 1.78/1.09  pred_elim:                              7
% 1.78/1.09  pred_elim_cl:                           6
% 1.78/1.09  pred_elim_cycles:                       10
% 1.78/1.09  merged_defs:                            8
% 1.78/1.09  merged_defs_ncl:                        0
% 1.78/1.09  bin_hyper_res:                          8
% 1.78/1.09  prep_cycles:                            4
% 1.78/1.09  pred_elim_time:                         0.067
% 1.78/1.09  splitting_time:                         0.
% 1.78/1.09  sem_filter_time:                        0.
% 1.78/1.09  monotx_time:                            0.
% 1.78/1.09  subtype_inf_time:                       0.
% 1.78/1.09  
% 1.78/1.09  ------ Problem properties
% 1.78/1.09  
% 1.78/1.09  clauses:                                27
% 1.78/1.09  conjectures:                            10
% 1.78/1.09  epr:                                    4
% 1.78/1.09  horn:                                   22
% 1.78/1.09  ground:                                 12
% 1.78/1.09  unary:                                  8
% 1.78/1.09  binary:                                 2
% 1.78/1.09  lits:                                   91
% 1.78/1.09  lits_eq:                                3
% 1.78/1.09  fd_pure:                                0
% 1.78/1.09  fd_pseudo:                              0
% 1.78/1.09  fd_cond:                                0
% 1.78/1.09  fd_pseudo_cond:                         0
% 1.78/1.09  ac_symbols:                             0
% 1.78/1.09  
% 1.78/1.09  ------ Propositional Solver
% 1.78/1.09  
% 1.78/1.09  prop_solver_calls:                      26
% 1.78/1.09  prop_fast_solver_calls:                 1709
% 1.78/1.09  smt_solver_calls:                       0
% 1.78/1.09  smt_fast_solver_calls:                  0
% 1.78/1.09  prop_num_of_clauses:                    799
% 1.78/1.09  prop_preprocess_simplified:             3862
% 1.78/1.09  prop_fo_subsumed:                       82
% 1.78/1.09  prop_solver_time:                       0.
% 1.78/1.09  smt_solver_time:                        0.
% 1.78/1.09  smt_fast_solver_time:                   0.
% 1.78/1.09  prop_fast_solver_time:                  0.
% 1.78/1.09  prop_unsat_core_time:                   0.
% 1.78/1.09  
% 1.78/1.09  ------ QBF
% 1.78/1.09  
% 1.78/1.09  qbf_q_res:                              0
% 1.78/1.09  qbf_num_tautologies:                    0
% 1.78/1.09  qbf_prep_cycles:                        0
% 1.78/1.09  
% 1.78/1.09  ------ BMC1
% 1.78/1.09  
% 1.78/1.09  bmc1_current_bound:                     -1
% 1.78/1.09  bmc1_last_solved_bound:                 -1
% 1.78/1.09  bmc1_unsat_core_size:                   -1
% 1.78/1.09  bmc1_unsat_core_parents_size:           -1
% 1.78/1.09  bmc1_merge_next_fun:                    0
% 1.78/1.09  bmc1_unsat_core_clauses_time:           0.
% 1.78/1.09  
% 1.78/1.09  ------ Instantiation
% 1.78/1.09  
% 1.78/1.09  inst_num_of_clauses:                    166
% 1.78/1.09  inst_num_in_passive:                    22
% 1.78/1.09  inst_num_in_active:                     137
% 1.78/1.09  inst_num_in_unprocessed:                6
% 1.78/1.09  inst_num_of_loops:                      147
% 1.78/1.09  inst_num_of_learning_restarts:          0
% 1.78/1.09  inst_num_moves_active_passive:          5
% 1.78/1.09  inst_lit_activity:                      0
% 1.78/1.09  inst_lit_activity_moves:                0
% 1.78/1.09  inst_num_tautologies:                   0
% 1.78/1.09  inst_num_prop_implied:                  0
% 1.78/1.09  inst_num_existing_simplified:           0
% 1.78/1.09  inst_num_eq_res_simplified:             0
% 1.78/1.09  inst_num_child_elim:                    0
% 1.78/1.09  inst_num_of_dismatching_blockings:      7
% 1.78/1.09  inst_num_of_non_proper_insts:           150
% 1.78/1.09  inst_num_of_duplicates:                 0
% 1.78/1.09  inst_inst_num_from_inst_to_res:         0
% 1.78/1.09  inst_dismatching_checking_time:         0.
% 1.78/1.09  
% 1.78/1.09  ------ Resolution
% 1.78/1.09  
% 1.78/1.09  res_num_of_clauses:                     0
% 1.78/1.09  res_num_in_passive:                     0
% 1.78/1.09  res_num_in_active:                      0
% 1.78/1.09  res_num_of_loops:                       137
% 1.78/1.09  res_forward_subset_subsumed:            43
% 1.78/1.09  res_backward_subset_subsumed:           0
% 1.78/1.09  res_forward_subsumed:                   1
% 1.78/1.09  res_backward_subsumed:                  0
% 1.78/1.09  res_forward_subsumption_resolution:     2
% 1.78/1.09  res_backward_subsumption_resolution:    2
% 1.78/1.09  res_clause_to_clause_subsumption:       141
% 1.78/1.09  res_orphan_elimination:                 0
% 1.78/1.09  res_tautology_del:                      61
% 1.78/1.09  res_num_eq_res_simplified:              2
% 1.78/1.09  res_num_sel_changes:                    0
% 1.78/1.09  res_moves_from_active_to_pass:          0
% 1.78/1.09  
% 1.78/1.09  ------ Superposition
% 1.78/1.09  
% 1.78/1.09  sup_time_total:                         0.
% 1.78/1.09  sup_time_generating:                    0.
% 1.78/1.09  sup_time_sim_full:                      0.
% 1.78/1.09  sup_time_sim_immed:                     0.
% 1.78/1.09  
% 1.78/1.09  sup_num_of_clauses:                     44
% 1.78/1.09  sup_num_in_active:                      28
% 1.78/1.09  sup_num_in_passive:                     16
% 1.78/1.09  sup_num_of_loops:                       28
% 1.78/1.09  sup_fw_superposition:                   17
% 1.78/1.09  sup_bw_superposition:                   6
% 1.78/1.09  sup_immediate_simplified:               4
% 1.78/1.09  sup_given_eliminated:                   0
% 1.78/1.09  comparisons_done:                       0
% 1.78/1.09  comparisons_avoided:                    0
% 1.78/1.09  
% 1.78/1.09  ------ Simplifications
% 1.78/1.09  
% 1.78/1.09  
% 1.78/1.09  sim_fw_subset_subsumed:                 4
% 1.78/1.09  sim_bw_subset_subsumed:                 0
% 1.78/1.09  sim_fw_subsumed:                        0
% 1.78/1.09  sim_bw_subsumed:                        0
% 1.78/1.09  sim_fw_subsumption_res:                 0
% 1.78/1.09  sim_bw_subsumption_res:                 0
% 1.78/1.09  sim_tautology_del:                      3
% 1.78/1.09  sim_eq_tautology_del:                   0
% 1.78/1.09  sim_eq_res_simp:                        0
% 1.78/1.09  sim_fw_demodulated:                     0
% 1.78/1.09  sim_bw_demodulated:                     0
% 1.78/1.09  sim_light_normalised:                   4
% 1.78/1.09  sim_joinable_taut:                      0
% 1.78/1.09  sim_joinable_simp:                      0
% 1.78/1.09  sim_ac_normalised:                      0
% 1.78/1.09  sim_smt_subsumption:                    0
% 1.78/1.09  
%------------------------------------------------------------------------------
