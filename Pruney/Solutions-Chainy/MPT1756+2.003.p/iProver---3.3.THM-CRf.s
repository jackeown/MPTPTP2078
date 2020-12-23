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
% DateTime   : Thu Dec  3 12:22:37 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  150 (1136 expanded)
%              Number of clauses        :   90 ( 157 expanded)
%              Number of leaves         :   13 ( 506 expanded)
%              Depth                    :   32
%              Number of atoms          : 1206 (22953 expanded)
%              Number of equality atoms :  132 (1469 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   44 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

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
    inference(negated_conjecture,[],[f7])).

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
    inference(ennf_transformation,[],[f8])).

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
    inference(nnf_transformation,[],[f19])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f32,plain,(
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
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6)
          | ~ r1_tmap_1(X1,X0,X2,X5) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6)
          | r1_tmap_1(X1,X0,X2,X5) )
        & sK6 = X5
        & r1_tarski(X4,u1_struct_0(X3))
        & r2_hidden(X5,X4)
        & v3_pre_topc(X4,X1)
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
              | ~ r1_tmap_1(X1,X0,X2,sK5) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
              | r1_tmap_1(X1,X0,X2,sK5) )
            & sK5 = X6
            & r1_tarski(X4,u1_struct_0(X3))
            & r2_hidden(sK5,X4)
            & v3_pre_topc(X4,X1)
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK5,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
                & r1_tarski(sK4,u1_struct_0(X3))
                & r2_hidden(X5,sK4)
                & v3_pre_topc(sK4,X1)
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
                    ( ( ~ r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X6)
                      | ~ r1_tmap_1(X1,X0,X2,X5) )
                    & ( r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X6)
                      | r1_tmap_1(X1,X0,X2,X5) )
                    & X5 = X6
                    & r1_tarski(X4,u1_struct_0(sK3))
                    & r2_hidden(X5,X4)
                    & v3_pre_topc(X4,X1)
                    & m1_subset_1(X6,u1_struct_0(sK3)) )
                & m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
                        ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X6)
                          | ~ r1_tmap_1(X1,X0,sK2,X5) )
                        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X6)
                          | r1_tmap_1(X1,X0,sK2,X5) )
                        & X5 = X6
                        & r1_tarski(X4,u1_struct_0(X3))
                        & r2_hidden(X5,X4)
                        & v3_pre_topc(X4,X1)
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
                            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X6)
                              | ~ r1_tmap_1(sK1,X0,X2,X5) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X6)
                              | r1_tmap_1(sK1,X0,X2,X5) )
                            & X5 = X6
                            & r1_tarski(X4,u1_struct_0(X3))
                            & r2_hidden(X5,X4)
                            & v3_pre_topc(X4,sK1)
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,u1_struct_0(sK1)) )
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
                & m1_pre_topc(X3,sK1)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
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
                              ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6)
                                | ~ r1_tmap_1(X1,sK0,X2,X5) )
                              & ( r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6)
                                | r1_tmap_1(X1,sK0,X2,X5) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK5) )
    & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
      | r1_tmap_1(sK1,sK0,sK2,sK5) )
    & sK5 = sK6
    & r1_tarski(sK4,u1_struct_0(sK3))
    & r2_hidden(sK5,sK4)
    & v3_pre_topc(sK4,sK1)
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f25,f32,f31,f30,f29,f28,f27,f26])).

fof(f58,plain,(
    v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

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
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
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
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
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
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
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
    inference(ennf_transformation,[],[f6])).

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

fof(f23,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
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
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

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
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
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

fof(f61,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1727,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK4),sK4)
    | ~ r1_tarski(sK4,k1_tops_1(sK1,sK4))
    | k1_tops_1(sK1,sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_15,negated_conjecture,
    ( v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,k1_tops_1(sK1,X0))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_371,plain,
    ( r1_tarski(sK4,k1_tops_1(sK1,X0))
    | ~ r1_tarski(sK4,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_24,c_18])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,k1_tops_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_371])).

cnf(c_1670,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK4,k1_tops_1(sK1,sK4))
    | ~ r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1669,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_392,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != sK4
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_393,plain,
    ( m1_connsp_2(X0,X1,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK5,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != sK4 ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f66])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_478,plain,
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
    | sK1 != X0
    | sK3 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_479,plain,
    ( r1_tmap_1(sK1,X0,X1,X2)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r1_tarski(X3,u1_struct_0(sK3))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_483,plain,
    ( ~ l1_pre_topc(X0)
    | r1_tmap_1(sK1,X0,X1,X2)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r1_tarski(X3,u1_struct_0(sK3))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_26,c_25,c_24,c_20])).

cnf(c_484,plain,
    ( r1_tmap_1(sK1,X0,X1,X2)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r1_tarski(X3,u1_struct_0(sK3))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_483])).

cnf(c_531,plain,
    ( r1_tmap_1(sK1,X0,X1,X2)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ m1_connsp_2(X3,sK1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r1_tarski(X3,u1_struct_0(sK3))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_484])).

cnf(c_532,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_connsp_2(X2,sK1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK3))
    | ~ v1_funct_1(sK2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_536,plain,
    ( ~ r1_tarski(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_connsp_2(X2,sK1,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | r1_tmap_1(sK1,X0,sK2,X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_532,c_23])).

cnf(c_537,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_connsp_2(X2,sK1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK3))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_536])).

cnf(c_676,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(X3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(X4,u1_struct_0(sK3))
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X0)
    | X4 != X2
    | k1_tops_1(X3,X2) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | sK5 != X1
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_393,c_537])).

cnf(c_677,plain,
    ( r1_tmap_1(sK1,X0,sK2,sK5)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(X1,u1_struct_0(sK3))
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,X1) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_681,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ r1_tarski(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r1_tmap_1(sK1,X0,sK2,sK5)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(X0)
    | k1_tops_1(sK1,X1) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_677,c_26,c_25,c_24,c_17])).

cnf(c_682,plain,
    ( r1_tmap_1(sK1,X0,sK2,sK5)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(X1,u1_struct_0(sK3))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k1_tops_1(sK1,X1) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_681])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_795,plain,
    ( r1_tmap_1(sK1,X0,sK2,sK5)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(X1,u1_struct_0(sK3))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k1_tops_1(sK1,X1) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_682,c_28])).

cnf(c_796,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ r1_tarski(X0,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK1,X0) != sK4
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_795])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_800,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ r1_tarski(X0,u1_struct_0(sK3))
    | k1_tops_1(sK1,X0) != sK4
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_796,c_29,c_27,c_21])).

cnf(c_801,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tarski(X0,u1_struct_0(sK3))
    | k1_tops_1(sK1,X0) != sK4
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_800])).

cnf(c_947,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tarski(X0,u1_struct_0(sK3))
    | k1_tops_1(sK1,X0) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_801])).

cnf(c_1079,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,u1_struct_0(sK3))
    | k1_tops_1(sK1,X0) != sK4
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_947])).

cnf(c_1666,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ sP0_iProver_split
    | k1_tops_1(sK1,sK4) != sK4 ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_895,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_896,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0),X0) ),
    inference(unflattening,[status(thm)],[c_895])).

cnf(c_1663,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_896])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_427,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
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
    | sK1 != X0
    | sK3 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_428,plain,
    ( ~ r1_tmap_1(sK1,X0,X1,X2)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r1_tarski(X3,u1_struct_0(sK3))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_432,plain,
    ( ~ l1_pre_topc(X0)
    | ~ r1_tmap_1(sK1,X0,X1,X2)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r1_tarski(X3,u1_struct_0(sK3))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_428,c_26,c_25,c_24,c_20])).

cnf(c_433,plain,
    ( ~ r1_tmap_1(sK1,X0,X1,X2)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r1_tarski(X3,u1_struct_0(sK3))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_432])).

cnf(c_579,plain,
    ( ~ r1_tmap_1(sK1,X0,X1,X2)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ m1_connsp_2(X3,sK1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r1_tarski(X3,u1_struct_0(sK3))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_433])).

cnf(c_580,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_connsp_2(X2,sK1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK3))
    | ~ v1_funct_1(sK2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_584,plain,
    ( ~ r1_tarski(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_connsp_2(X2,sK1,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ r1_tmap_1(sK1,X0,sK2,X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_580,c_23])).

cnf(c_585,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_connsp_2(X2,sK1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK3))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_584])).

cnf(c_631,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(X3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(X4,u1_struct_0(sK3))
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X0)
    | X4 != X2
    | k1_tops_1(X3,X2) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | sK5 != X1
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_393,c_585])).

cnf(c_632,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,sK5)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(X1,u1_struct_0(sK3))
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,X1) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_636,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ r1_tarski(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,X0,sK2,sK5)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(X0)
    | k1_tops_1(sK1,X1) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_632,c_26,c_25,c_24,c_17])).

cnf(c_637,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,sK5)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(X1,u1_struct_0(sK3))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k1_tops_1(sK1,X1) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_636])).

cnf(c_828,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,sK5)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(X1,u1_struct_0(sK3))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k1_tops_1(sK1,X1) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_637,c_28])).

cnf(c_829,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ r1_tarski(X0,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK1,X0) != sK4
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_828])).

cnf(c_833,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ r1_tarski(X0,u1_struct_0(sK3))
    | k1_tops_1(sK1,X0) != sK4
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_829,c_29,c_27,c_21])).

cnf(c_834,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tarski(X0,u1_struct_0(sK3))
    | k1_tops_1(sK1,X0) != sK4
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_833])).

cnf(c_943,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tarski(X0,u1_struct_0(sK3))
    | k1_tops_1(sK1,X0) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_834])).

cnf(c_1081,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_943])).

cnf(c_1528,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1081])).

cnf(c_12,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1607,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK6) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1528,c_12])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1540,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1080,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_947])).

cnf(c_1526,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1080])).

cnf(c_1599,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK6) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1526,c_12])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1543,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1580,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK6) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1543,c_12])).

cnf(c_1604,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1599,c_1540,c_1580])).

cnf(c_11,negated_conjecture,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1542,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1575,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK6) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1542,c_12])).

cnf(c_1612,plain,
    ( sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1607,c_1540,c_1604,c_1575])).

cnf(c_1621,plain,
    ( sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1612])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1727,c_1670,c_1669,c_1666,c_1663,c_1621,c_13,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.73/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.00  
% 1.73/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.73/1.00  
% 1.73/1.00  ------  iProver source info
% 1.73/1.00  
% 1.73/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.73/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.73/1.00  git: non_committed_changes: false
% 1.73/1.00  git: last_make_outside_of_git: false
% 1.73/1.00  
% 1.73/1.00  ------ 
% 1.73/1.00  
% 1.73/1.00  ------ Input Options
% 1.73/1.00  
% 1.73/1.00  --out_options                           all
% 1.73/1.00  --tptp_safe_out                         true
% 1.73/1.00  --problem_path                          ""
% 1.73/1.00  --include_path                          ""
% 1.73/1.00  --clausifier                            res/vclausify_rel
% 1.73/1.00  --clausifier_options                    --mode clausify
% 1.73/1.00  --stdin                                 false
% 1.73/1.00  --stats_out                             all
% 1.73/1.00  
% 1.73/1.00  ------ General Options
% 1.73/1.00  
% 1.73/1.00  --fof                                   false
% 1.73/1.00  --time_out_real                         305.
% 1.73/1.00  --time_out_virtual                      -1.
% 1.73/1.00  --symbol_type_check                     false
% 1.73/1.00  --clausify_out                          false
% 1.73/1.00  --sig_cnt_out                           false
% 1.73/1.00  --trig_cnt_out                          false
% 1.73/1.00  --trig_cnt_out_tolerance                1.
% 1.73/1.00  --trig_cnt_out_sk_spl                   false
% 1.73/1.00  --abstr_cl_out                          false
% 1.73/1.00  
% 1.73/1.00  ------ Global Options
% 1.73/1.00  
% 1.73/1.00  --schedule                              default
% 1.73/1.00  --add_important_lit                     false
% 1.73/1.00  --prop_solver_per_cl                    1000
% 1.73/1.00  --min_unsat_core                        false
% 1.73/1.00  --soft_assumptions                      false
% 1.73/1.00  --soft_lemma_size                       3
% 1.73/1.00  --prop_impl_unit_size                   0
% 1.73/1.00  --prop_impl_unit                        []
% 1.73/1.00  --share_sel_clauses                     true
% 1.73/1.00  --reset_solvers                         false
% 1.73/1.00  --bc_imp_inh                            [conj_cone]
% 1.73/1.00  --conj_cone_tolerance                   3.
% 1.73/1.00  --extra_neg_conj                        none
% 1.73/1.00  --large_theory_mode                     true
% 1.73/1.00  --prolific_symb_bound                   200
% 1.73/1.00  --lt_threshold                          2000
% 1.73/1.00  --clause_weak_htbl                      true
% 1.73/1.00  --gc_record_bc_elim                     false
% 1.73/1.00  
% 1.73/1.00  ------ Preprocessing Options
% 1.73/1.00  
% 1.73/1.00  --preprocessing_flag                    true
% 1.73/1.00  --time_out_prep_mult                    0.1
% 1.73/1.00  --splitting_mode                        input
% 1.73/1.00  --splitting_grd                         true
% 1.73/1.00  --splitting_cvd                         false
% 1.73/1.00  --splitting_cvd_svl                     false
% 1.73/1.00  --splitting_nvd                         32
% 1.73/1.00  --sub_typing                            true
% 1.73/1.00  --prep_gs_sim                           true
% 1.73/1.00  --prep_unflatten                        true
% 1.73/1.00  --prep_res_sim                          true
% 1.73/1.00  --prep_upred                            true
% 1.73/1.00  --prep_sem_filter                       exhaustive
% 1.73/1.00  --prep_sem_filter_out                   false
% 1.73/1.00  --pred_elim                             true
% 1.73/1.00  --res_sim_input                         true
% 1.73/1.00  --eq_ax_congr_red                       true
% 1.73/1.00  --pure_diseq_elim                       true
% 1.73/1.00  --brand_transform                       false
% 1.73/1.00  --non_eq_to_eq                          false
% 1.73/1.00  --prep_def_merge                        true
% 1.73/1.00  --prep_def_merge_prop_impl              false
% 1.73/1.00  --prep_def_merge_mbd                    true
% 1.73/1.00  --prep_def_merge_tr_red                 false
% 1.73/1.00  --prep_def_merge_tr_cl                  false
% 1.73/1.00  --smt_preprocessing                     true
% 1.73/1.00  --smt_ac_axioms                         fast
% 1.73/1.00  --preprocessed_out                      false
% 1.73/1.00  --preprocessed_stats                    false
% 1.73/1.00  
% 1.73/1.00  ------ Abstraction refinement Options
% 1.73/1.00  
% 1.73/1.00  --abstr_ref                             []
% 1.73/1.00  --abstr_ref_prep                        false
% 1.73/1.00  --abstr_ref_until_sat                   false
% 1.73/1.00  --abstr_ref_sig_restrict                funpre
% 1.73/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.73/1.00  --abstr_ref_under                       []
% 1.73/1.00  
% 1.73/1.00  ------ SAT Options
% 1.73/1.00  
% 1.73/1.00  --sat_mode                              false
% 1.73/1.00  --sat_fm_restart_options                ""
% 1.73/1.00  --sat_gr_def                            false
% 1.73/1.00  --sat_epr_types                         true
% 1.73/1.00  --sat_non_cyclic_types                  false
% 1.73/1.00  --sat_finite_models                     false
% 1.73/1.00  --sat_fm_lemmas                         false
% 1.73/1.00  --sat_fm_prep                           false
% 1.73/1.00  --sat_fm_uc_incr                        true
% 1.73/1.00  --sat_out_model                         small
% 1.73/1.00  --sat_out_clauses                       false
% 1.73/1.00  
% 1.73/1.00  ------ QBF Options
% 1.73/1.00  
% 1.73/1.00  --qbf_mode                              false
% 1.73/1.00  --qbf_elim_univ                         false
% 1.73/1.00  --qbf_dom_inst                          none
% 1.73/1.00  --qbf_dom_pre_inst                      false
% 1.73/1.00  --qbf_sk_in                             false
% 1.73/1.00  --qbf_pred_elim                         true
% 1.73/1.00  --qbf_split                             512
% 1.73/1.00  
% 1.73/1.00  ------ BMC1 Options
% 1.73/1.00  
% 1.73/1.00  --bmc1_incremental                      false
% 1.73/1.00  --bmc1_axioms                           reachable_all
% 1.73/1.00  --bmc1_min_bound                        0
% 1.73/1.00  --bmc1_max_bound                        -1
% 1.73/1.00  --bmc1_max_bound_default                -1
% 1.73/1.00  --bmc1_symbol_reachability              true
% 1.73/1.00  --bmc1_property_lemmas                  false
% 1.73/1.00  --bmc1_k_induction                      false
% 1.73/1.00  --bmc1_non_equiv_states                 false
% 1.73/1.00  --bmc1_deadlock                         false
% 1.73/1.00  --bmc1_ucm                              false
% 1.73/1.00  --bmc1_add_unsat_core                   none
% 1.73/1.00  --bmc1_unsat_core_children              false
% 1.73/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.73/1.00  --bmc1_out_stat                         full
% 1.73/1.00  --bmc1_ground_init                      false
% 1.73/1.00  --bmc1_pre_inst_next_state              false
% 1.73/1.00  --bmc1_pre_inst_state                   false
% 1.73/1.00  --bmc1_pre_inst_reach_state             false
% 1.73/1.00  --bmc1_out_unsat_core                   false
% 1.73/1.00  --bmc1_aig_witness_out                  false
% 1.73/1.00  --bmc1_verbose                          false
% 1.73/1.00  --bmc1_dump_clauses_tptp                false
% 1.73/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.73/1.00  --bmc1_dump_file                        -
% 1.73/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.73/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.73/1.00  --bmc1_ucm_extend_mode                  1
% 1.73/1.00  --bmc1_ucm_init_mode                    2
% 1.73/1.00  --bmc1_ucm_cone_mode                    none
% 1.73/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.73/1.00  --bmc1_ucm_relax_model                  4
% 1.73/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.73/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.73/1.00  --bmc1_ucm_layered_model                none
% 1.73/1.00  --bmc1_ucm_max_lemma_size               10
% 1.73/1.00  
% 1.73/1.00  ------ AIG Options
% 1.73/1.00  
% 1.73/1.00  --aig_mode                              false
% 1.73/1.00  
% 1.73/1.00  ------ Instantiation Options
% 1.73/1.00  
% 1.73/1.00  --instantiation_flag                    true
% 1.73/1.00  --inst_sos_flag                         false
% 1.73/1.00  --inst_sos_phase                        true
% 1.73/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.73/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.73/1.00  --inst_lit_sel_side                     num_symb
% 1.73/1.00  --inst_solver_per_active                1400
% 1.73/1.00  --inst_solver_calls_frac                1.
% 1.73/1.00  --inst_passive_queue_type               priority_queues
% 1.73/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.73/1.00  --inst_passive_queues_freq              [25;2]
% 1.73/1.00  --inst_dismatching                      true
% 1.73/1.00  --inst_eager_unprocessed_to_passive     true
% 1.73/1.00  --inst_prop_sim_given                   true
% 1.73/1.00  --inst_prop_sim_new                     false
% 1.73/1.00  --inst_subs_new                         false
% 1.73/1.00  --inst_eq_res_simp                      false
% 1.73/1.00  --inst_subs_given                       false
% 1.73/1.00  --inst_orphan_elimination               true
% 1.73/1.00  --inst_learning_loop_flag               true
% 1.73/1.00  --inst_learning_start                   3000
% 1.73/1.00  --inst_learning_factor                  2
% 1.73/1.00  --inst_start_prop_sim_after_learn       3
% 1.73/1.00  --inst_sel_renew                        solver
% 1.73/1.00  --inst_lit_activity_flag                true
% 1.73/1.00  --inst_restr_to_given                   false
% 1.73/1.00  --inst_activity_threshold               500
% 1.73/1.00  --inst_out_proof                        true
% 1.73/1.00  
% 1.73/1.00  ------ Resolution Options
% 1.73/1.00  
% 1.73/1.00  --resolution_flag                       true
% 1.73/1.00  --res_lit_sel                           adaptive
% 1.73/1.00  --res_lit_sel_side                      none
% 1.73/1.00  --res_ordering                          kbo
% 1.73/1.00  --res_to_prop_solver                    active
% 1.73/1.00  --res_prop_simpl_new                    false
% 1.73/1.00  --res_prop_simpl_given                  true
% 1.73/1.00  --res_passive_queue_type                priority_queues
% 1.73/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.73/1.00  --res_passive_queues_freq               [15;5]
% 1.73/1.00  --res_forward_subs                      full
% 1.73/1.00  --res_backward_subs                     full
% 1.73/1.00  --res_forward_subs_resolution           true
% 1.73/1.00  --res_backward_subs_resolution          true
% 1.73/1.00  --res_orphan_elimination                true
% 1.73/1.00  --res_time_limit                        2.
% 1.73/1.00  --res_out_proof                         true
% 1.73/1.00  
% 1.73/1.00  ------ Superposition Options
% 1.73/1.00  
% 1.73/1.00  --superposition_flag                    true
% 1.73/1.00  --sup_passive_queue_type                priority_queues
% 1.73/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.73/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.73/1.00  --demod_completeness_check              fast
% 1.73/1.00  --demod_use_ground                      true
% 1.73/1.00  --sup_to_prop_solver                    passive
% 1.73/1.00  --sup_prop_simpl_new                    true
% 1.73/1.00  --sup_prop_simpl_given                  true
% 1.73/1.00  --sup_fun_splitting                     false
% 1.73/1.00  --sup_smt_interval                      50000
% 1.73/1.00  
% 1.73/1.00  ------ Superposition Simplification Setup
% 1.73/1.00  
% 1.73/1.00  --sup_indices_passive                   []
% 1.73/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.73/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.00  --sup_full_bw                           [BwDemod]
% 1.73/1.00  --sup_immed_triv                        [TrivRules]
% 1.73/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.73/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.00  --sup_immed_bw_main                     []
% 1.73/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.73/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.00  
% 1.73/1.00  ------ Combination Options
% 1.73/1.00  
% 1.73/1.00  --comb_res_mult                         3
% 1.73/1.00  --comb_sup_mult                         2
% 1.73/1.00  --comb_inst_mult                        10
% 1.73/1.00  
% 1.73/1.00  ------ Debug Options
% 1.73/1.00  
% 1.73/1.00  --dbg_backtrace                         false
% 1.73/1.00  --dbg_dump_prop_clauses                 false
% 1.73/1.00  --dbg_dump_prop_clauses_file            -
% 1.73/1.00  --dbg_out_stat                          false
% 1.73/1.00  ------ Parsing...
% 1.73/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.73/1.00  
% 1.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.73/1.00  
% 1.73/1.00  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.73/1.00  
% 1.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.73/1.00  ------ Proving...
% 1.73/1.00  ------ Problem Properties 
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  clauses                                 21
% 1.73/1.00  conjectures                             8
% 1.73/1.00  EPR                                     3
% 1.73/1.00  Horn                                    16
% 1.73/1.00  unary                                   7
% 1.73/1.00  binary                                  4
% 1.73/1.00  lits                                    57
% 1.73/1.00  lits eq                                 8
% 1.73/1.00  fd_pure                                 0
% 1.73/1.00  fd_pseudo                               0
% 1.73/1.00  fd_cond                                 0
% 1.73/1.00  fd_pseudo_cond                          1
% 1.73/1.00  AC symbols                              0
% 1.73/1.00  
% 1.73/1.00  ------ Schedule dynamic 5 is on 
% 1.73/1.00  
% 1.73/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  ------ 
% 1.73/1.00  Current options:
% 1.73/1.00  ------ 
% 1.73/1.00  
% 1.73/1.00  ------ Input Options
% 1.73/1.00  
% 1.73/1.00  --out_options                           all
% 1.73/1.00  --tptp_safe_out                         true
% 1.73/1.00  --problem_path                          ""
% 1.73/1.00  --include_path                          ""
% 1.73/1.00  --clausifier                            res/vclausify_rel
% 1.73/1.00  --clausifier_options                    --mode clausify
% 1.73/1.00  --stdin                                 false
% 1.73/1.00  --stats_out                             all
% 1.73/1.00  
% 1.73/1.00  ------ General Options
% 1.73/1.00  
% 1.73/1.00  --fof                                   false
% 1.73/1.00  --time_out_real                         305.
% 1.73/1.00  --time_out_virtual                      -1.
% 1.73/1.00  --symbol_type_check                     false
% 1.73/1.00  --clausify_out                          false
% 1.73/1.00  --sig_cnt_out                           false
% 1.73/1.00  --trig_cnt_out                          false
% 1.73/1.00  --trig_cnt_out_tolerance                1.
% 1.73/1.00  --trig_cnt_out_sk_spl                   false
% 1.73/1.00  --abstr_cl_out                          false
% 1.73/1.00  
% 1.73/1.00  ------ Global Options
% 1.73/1.00  
% 1.73/1.00  --schedule                              default
% 1.73/1.00  --add_important_lit                     false
% 1.73/1.00  --prop_solver_per_cl                    1000
% 1.73/1.00  --min_unsat_core                        false
% 1.73/1.00  --soft_assumptions                      false
% 1.73/1.00  --soft_lemma_size                       3
% 1.73/1.00  --prop_impl_unit_size                   0
% 1.73/1.00  --prop_impl_unit                        []
% 1.73/1.00  --share_sel_clauses                     true
% 1.73/1.00  --reset_solvers                         false
% 1.73/1.00  --bc_imp_inh                            [conj_cone]
% 1.73/1.00  --conj_cone_tolerance                   3.
% 1.73/1.00  --extra_neg_conj                        none
% 1.73/1.00  --large_theory_mode                     true
% 1.73/1.00  --prolific_symb_bound                   200
% 1.73/1.00  --lt_threshold                          2000
% 1.73/1.00  --clause_weak_htbl                      true
% 1.73/1.00  --gc_record_bc_elim                     false
% 1.73/1.00  
% 1.73/1.00  ------ Preprocessing Options
% 1.73/1.00  
% 1.73/1.00  --preprocessing_flag                    true
% 1.73/1.00  --time_out_prep_mult                    0.1
% 1.73/1.00  --splitting_mode                        input
% 1.73/1.00  --splitting_grd                         true
% 1.73/1.00  --splitting_cvd                         false
% 1.73/1.00  --splitting_cvd_svl                     false
% 1.73/1.00  --splitting_nvd                         32
% 1.73/1.00  --sub_typing                            true
% 1.73/1.00  --prep_gs_sim                           true
% 1.73/1.00  --prep_unflatten                        true
% 1.73/1.00  --prep_res_sim                          true
% 1.73/1.00  --prep_upred                            true
% 1.73/1.00  --prep_sem_filter                       exhaustive
% 1.73/1.00  --prep_sem_filter_out                   false
% 1.73/1.00  --pred_elim                             true
% 1.73/1.00  --res_sim_input                         true
% 1.73/1.00  --eq_ax_congr_red                       true
% 1.73/1.00  --pure_diseq_elim                       true
% 1.73/1.00  --brand_transform                       false
% 1.73/1.00  --non_eq_to_eq                          false
% 1.73/1.00  --prep_def_merge                        true
% 1.73/1.00  --prep_def_merge_prop_impl              false
% 1.73/1.00  --prep_def_merge_mbd                    true
% 1.73/1.00  --prep_def_merge_tr_red                 false
% 1.73/1.00  --prep_def_merge_tr_cl                  false
% 1.73/1.00  --smt_preprocessing                     true
% 1.73/1.00  --smt_ac_axioms                         fast
% 1.73/1.00  --preprocessed_out                      false
% 1.73/1.00  --preprocessed_stats                    false
% 1.73/1.00  
% 1.73/1.00  ------ Abstraction refinement Options
% 1.73/1.00  
% 1.73/1.00  --abstr_ref                             []
% 1.73/1.00  --abstr_ref_prep                        false
% 1.73/1.00  --abstr_ref_until_sat                   false
% 1.73/1.00  --abstr_ref_sig_restrict                funpre
% 1.73/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.73/1.00  --abstr_ref_under                       []
% 1.73/1.00  
% 1.73/1.00  ------ SAT Options
% 1.73/1.00  
% 1.73/1.00  --sat_mode                              false
% 1.73/1.00  --sat_fm_restart_options                ""
% 1.73/1.00  --sat_gr_def                            false
% 1.73/1.00  --sat_epr_types                         true
% 1.73/1.00  --sat_non_cyclic_types                  false
% 1.73/1.00  --sat_finite_models                     false
% 1.73/1.00  --sat_fm_lemmas                         false
% 1.73/1.00  --sat_fm_prep                           false
% 1.73/1.00  --sat_fm_uc_incr                        true
% 1.73/1.00  --sat_out_model                         small
% 1.73/1.00  --sat_out_clauses                       false
% 1.73/1.00  
% 1.73/1.00  ------ QBF Options
% 1.73/1.00  
% 1.73/1.00  --qbf_mode                              false
% 1.73/1.00  --qbf_elim_univ                         false
% 1.73/1.00  --qbf_dom_inst                          none
% 1.73/1.00  --qbf_dom_pre_inst                      false
% 1.73/1.00  --qbf_sk_in                             false
% 1.73/1.00  --qbf_pred_elim                         true
% 1.73/1.00  --qbf_split                             512
% 1.73/1.00  
% 1.73/1.00  ------ BMC1 Options
% 1.73/1.00  
% 1.73/1.00  --bmc1_incremental                      false
% 1.73/1.00  --bmc1_axioms                           reachable_all
% 1.73/1.00  --bmc1_min_bound                        0
% 1.73/1.00  --bmc1_max_bound                        -1
% 1.73/1.00  --bmc1_max_bound_default                -1
% 1.73/1.00  --bmc1_symbol_reachability              true
% 1.73/1.00  --bmc1_property_lemmas                  false
% 1.73/1.00  --bmc1_k_induction                      false
% 1.73/1.00  --bmc1_non_equiv_states                 false
% 1.73/1.00  --bmc1_deadlock                         false
% 1.73/1.00  --bmc1_ucm                              false
% 1.73/1.00  --bmc1_add_unsat_core                   none
% 1.73/1.00  --bmc1_unsat_core_children              false
% 1.73/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.73/1.00  --bmc1_out_stat                         full
% 1.73/1.00  --bmc1_ground_init                      false
% 1.73/1.00  --bmc1_pre_inst_next_state              false
% 1.73/1.00  --bmc1_pre_inst_state                   false
% 1.73/1.00  --bmc1_pre_inst_reach_state             false
% 1.73/1.00  --bmc1_out_unsat_core                   false
% 1.73/1.00  --bmc1_aig_witness_out                  false
% 1.73/1.00  --bmc1_verbose                          false
% 1.73/1.00  --bmc1_dump_clauses_tptp                false
% 1.73/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.73/1.00  --bmc1_dump_file                        -
% 1.73/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.73/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.73/1.00  --bmc1_ucm_extend_mode                  1
% 1.73/1.00  --bmc1_ucm_init_mode                    2
% 1.73/1.00  --bmc1_ucm_cone_mode                    none
% 1.73/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.73/1.00  --bmc1_ucm_relax_model                  4
% 1.73/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.73/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.73/1.00  --bmc1_ucm_layered_model                none
% 1.73/1.00  --bmc1_ucm_max_lemma_size               10
% 1.73/1.00  
% 1.73/1.00  ------ AIG Options
% 1.73/1.00  
% 1.73/1.00  --aig_mode                              false
% 1.73/1.00  
% 1.73/1.00  ------ Instantiation Options
% 1.73/1.00  
% 1.73/1.00  --instantiation_flag                    true
% 1.73/1.00  --inst_sos_flag                         false
% 1.73/1.00  --inst_sos_phase                        true
% 1.73/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.73/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.73/1.00  --inst_lit_sel_side                     none
% 1.73/1.00  --inst_solver_per_active                1400
% 1.73/1.00  --inst_solver_calls_frac                1.
% 1.73/1.00  --inst_passive_queue_type               priority_queues
% 1.73/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.73/1.00  --inst_passive_queues_freq              [25;2]
% 1.73/1.00  --inst_dismatching                      true
% 1.73/1.00  --inst_eager_unprocessed_to_passive     true
% 1.73/1.00  --inst_prop_sim_given                   true
% 1.73/1.00  --inst_prop_sim_new                     false
% 1.73/1.00  --inst_subs_new                         false
% 1.73/1.00  --inst_eq_res_simp                      false
% 1.73/1.00  --inst_subs_given                       false
% 1.73/1.00  --inst_orphan_elimination               true
% 1.73/1.00  --inst_learning_loop_flag               true
% 1.73/1.00  --inst_learning_start                   3000
% 1.73/1.00  --inst_learning_factor                  2
% 1.73/1.00  --inst_start_prop_sim_after_learn       3
% 1.73/1.00  --inst_sel_renew                        solver
% 1.73/1.00  --inst_lit_activity_flag                true
% 1.73/1.00  --inst_restr_to_given                   false
% 1.73/1.00  --inst_activity_threshold               500
% 1.73/1.00  --inst_out_proof                        true
% 1.73/1.00  
% 1.73/1.00  ------ Resolution Options
% 1.73/1.00  
% 1.73/1.00  --resolution_flag                       false
% 1.73/1.00  --res_lit_sel                           adaptive
% 1.73/1.00  --res_lit_sel_side                      none
% 1.73/1.00  --res_ordering                          kbo
% 1.73/1.00  --res_to_prop_solver                    active
% 1.73/1.00  --res_prop_simpl_new                    false
% 1.73/1.00  --res_prop_simpl_given                  true
% 1.73/1.00  --res_passive_queue_type                priority_queues
% 1.73/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.73/1.00  --res_passive_queues_freq               [15;5]
% 1.73/1.00  --res_forward_subs                      full
% 1.73/1.00  --res_backward_subs                     full
% 1.73/1.00  --res_forward_subs_resolution           true
% 1.73/1.00  --res_backward_subs_resolution          true
% 1.73/1.00  --res_orphan_elimination                true
% 1.73/1.00  --res_time_limit                        2.
% 1.73/1.00  --res_out_proof                         true
% 1.73/1.00  
% 1.73/1.00  ------ Superposition Options
% 1.73/1.00  
% 1.73/1.00  --superposition_flag                    true
% 1.73/1.00  --sup_passive_queue_type                priority_queues
% 1.73/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.73/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.73/1.00  --demod_completeness_check              fast
% 1.73/1.00  --demod_use_ground                      true
% 1.73/1.00  --sup_to_prop_solver                    passive
% 1.73/1.00  --sup_prop_simpl_new                    true
% 1.73/1.00  --sup_prop_simpl_given                  true
% 1.73/1.00  --sup_fun_splitting                     false
% 1.73/1.00  --sup_smt_interval                      50000
% 1.73/1.00  
% 1.73/1.00  ------ Superposition Simplification Setup
% 1.73/1.00  
% 1.73/1.00  --sup_indices_passive                   []
% 1.73/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.73/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.00  --sup_full_bw                           [BwDemod]
% 1.73/1.00  --sup_immed_triv                        [TrivRules]
% 1.73/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.73/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.00  --sup_immed_bw_main                     []
% 1.73/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.73/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.00  
% 1.73/1.00  ------ Combination Options
% 1.73/1.00  
% 1.73/1.00  --comb_res_mult                         3
% 1.73/1.00  --comb_sup_mult                         2
% 1.73/1.00  --comb_inst_mult                        10
% 1.73/1.00  
% 1.73/1.00  ------ Debug Options
% 1.73/1.00  
% 1.73/1.00  --dbg_backtrace                         false
% 1.73/1.00  --dbg_dump_prop_clauses                 false
% 1.73/1.00  --dbg_dump_prop_clauses_file            -
% 1.73/1.00  --dbg_out_stat                          false
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  ------ Proving...
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  % SZS status Theorem for theBenchmark.p
% 1.73/1.00  
% 1.73/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.73/1.00  
% 1.73/1.00  fof(f1,axiom,(
% 1.73/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f20,plain,(
% 1.73/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.73/1.00    inference(nnf_transformation,[],[f1])).
% 1.73/1.00  
% 1.73/1.00  fof(f21,plain,(
% 1.73/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.73/1.00    inference(flattening,[],[f20])).
% 1.73/1.00  
% 1.73/1.00  fof(f36,plain,(
% 1.73/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f21])).
% 1.73/1.00  
% 1.73/1.00  fof(f3,axiom,(
% 1.73/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f10,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/1.00    inference(ennf_transformation,[],[f3])).
% 1.73/1.00  
% 1.73/1.00  fof(f11,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/1.00    inference(flattening,[],[f10])).
% 1.73/1.00  
% 1.73/1.00  fof(f38,plain,(
% 1.73/1.00    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f11])).
% 1.73/1.00  
% 1.73/1.00  fof(f7,conjecture,(
% 1.73/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f8,negated_conjecture,(
% 1.73/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.73/1.00    inference(negated_conjecture,[],[f7])).
% 1.73/1.00  
% 1.73/1.00  fof(f18,plain,(
% 1.73/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.73/1.00    inference(ennf_transformation,[],[f8])).
% 1.73/1.00  
% 1.73/1.00  fof(f19,plain,(
% 1.73/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.73/1.00    inference(flattening,[],[f18])).
% 1.73/1.00  
% 1.73/1.00  fof(f24,plain,(
% 1.73/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5))) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.73/1.00    inference(nnf_transformation,[],[f19])).
% 1.73/1.00  
% 1.73/1.00  fof(f25,plain,(
% 1.73/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.73/1.00    inference(flattening,[],[f24])).
% 1.73/1.00  
% 1.73/1.00  fof(f32,plain,(
% 1.73/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | r1_tmap_1(X1,X0,X2,X5)) & sK6 = X5 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 1.73/1.00    introduced(choice_axiom,[])).
% 1.73/1.00  
% 1.73/1.00  fof(f31,plain,(
% 1.73/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,sK5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,sK5)) & sK5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(sK5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,u1_struct_0(X1)))) )),
% 1.73/1.00    introduced(choice_axiom,[])).
% 1.73/1.00  
% 1.73/1.00  fof(f30,plain,(
% 1.73/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(sK4,u1_struct_0(X3)) & r2_hidden(X5,sK4) & v3_pre_topc(sK4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 1.73/1.00    introduced(choice_axiom,[])).
% 1.73/1.00  
% 1.73/1.00  fof(f29,plain,(
% 1.73/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(sK3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 1.73/1.00    introduced(choice_axiom,[])).
% 1.73/1.00  
% 1.73/1.00  fof(f28,plain,(
% 1.73/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X6) | ~r1_tmap_1(X1,X0,sK2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X6) | r1_tmap_1(X1,X0,sK2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK2))) )),
% 1.73/1.00    introduced(choice_axiom,[])).
% 1.73/1.00  
% 1.73/1.00  fof(f27,plain,(
% 1.73/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X6) | ~r1_tmap_1(sK1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X6) | r1_tmap_1(sK1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.73/1.00    introduced(choice_axiom,[])).
% 1.73/1.00  
% 1.73/1.00  fof(f26,plain,(
% 1.73/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6) | ~r1_tmap_1(X1,sK0,X2,X5)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6) | r1_tmap_1(X1,sK0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.73/1.00    introduced(choice_axiom,[])).
% 1.73/1.00  
% 1.73/1.00  fof(f33,plain,(
% 1.73/1.00    (((((((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)) & sK5 = sK6 & r1_tarski(sK4,u1_struct_0(sK3)) & r2_hidden(sK5,sK4) & v3_pre_topc(sK4,sK1) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f25,f32,f31,f30,f29,f28,f27,f26])).
% 1.73/1.00  
% 1.73/1.00  fof(f58,plain,(
% 1.73/1.00    v3_pre_topc(sK4,sK1)),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f49,plain,(
% 1.73/1.00    l1_pre_topc(sK1)),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f55,plain,(
% 1.73/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f34,plain,(
% 1.73/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.73/1.00    inference(cnf_transformation,[],[f21])).
% 1.73/1.00  
% 1.73/1.00  fof(f65,plain,(
% 1.73/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.73/1.00    inference(equality_resolution,[],[f34])).
% 1.73/1.00  
% 1.73/1.00  fof(f4,axiom,(
% 1.73/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f12,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.73/1.00    inference(ennf_transformation,[],[f4])).
% 1.73/1.00  
% 1.73/1.00  fof(f13,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/1.00    inference(flattening,[],[f12])).
% 1.73/1.00  
% 1.73/1.00  fof(f22,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/1.00    inference(nnf_transformation,[],[f13])).
% 1.73/1.00  
% 1.73/1.00  fof(f40,plain,(
% 1.73/1.00    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f22])).
% 1.73/1.00  
% 1.73/1.00  fof(f59,plain,(
% 1.73/1.00    r2_hidden(sK5,sK4)),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f51,plain,(
% 1.73/1.00    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f6,axiom,(
% 1.73/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f16,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.73/1.00    inference(ennf_transformation,[],[f6])).
% 1.73/1.00  
% 1.73/1.00  fof(f17,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/1.00    inference(flattening,[],[f16])).
% 1.73/1.00  
% 1.73/1.00  fof(f23,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/1.00    inference(nnf_transformation,[],[f17])).
% 1.73/1.00  
% 1.73/1.00  fof(f43,plain,(
% 1.73/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f23])).
% 1.73/1.00  
% 1.73/1.00  fof(f66,plain,(
% 1.73/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/1.00    inference(equality_resolution,[],[f43])).
% 1.73/1.00  
% 1.73/1.00  fof(f54,plain,(
% 1.73/1.00    m1_pre_topc(sK3,sK1)),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f47,plain,(
% 1.73/1.00    ~v2_struct_0(sK1)),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f48,plain,(
% 1.73/1.00    v2_pre_topc(sK1)),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f53,plain,(
% 1.73/1.00    ~v2_struct_0(sK3)),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f50,plain,(
% 1.73/1.00    v1_funct_1(sK2)),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f56,plain,(
% 1.73/1.00    m1_subset_1(sK5,u1_struct_0(sK1))),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f45,plain,(
% 1.73/1.00    v2_pre_topc(sK0)),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f44,plain,(
% 1.73/1.00    ~v2_struct_0(sK0)),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f46,plain,(
% 1.73/1.00    l1_pre_topc(sK0)),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f52,plain,(
% 1.73/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f2,axiom,(
% 1.73/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f9,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/1.00    inference(ennf_transformation,[],[f2])).
% 1.73/1.00  
% 1.73/1.00  fof(f37,plain,(
% 1.73/1.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f9])).
% 1.73/1.00  
% 1.73/1.00  fof(f42,plain,(
% 1.73/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f23])).
% 1.73/1.00  
% 1.73/1.00  fof(f67,plain,(
% 1.73/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/1.00    inference(equality_resolution,[],[f42])).
% 1.73/1.00  
% 1.73/1.00  fof(f61,plain,(
% 1.73/1.00    sK5 = sK6),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f57,plain,(
% 1.73/1.00    m1_subset_1(sK6,u1_struct_0(sK3))),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f63,plain,(
% 1.73/1.00    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f62,plain,(
% 1.73/1.00    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f60,plain,(
% 1.73/1.00    r1_tarski(sK4,u1_struct_0(sK3))),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  cnf(c_0,plain,
% 1.73/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.73/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1727,plain,
% 1.73/1.00      ( ~ r1_tarski(k1_tops_1(sK1,sK4),sK4)
% 1.73/1.00      | ~ r1_tarski(sK4,k1_tops_1(sK1,sK4))
% 1.73/1.00      | k1_tops_1(sK1,sK4) = sK4 ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_4,plain,
% 1.73/1.00      ( ~ v3_pre_topc(X0,X1)
% 1.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ r1_tarski(X0,X2)
% 1.73/1.00      | r1_tarski(X0,k1_tops_1(X1,X2))
% 1.73/1.00      | ~ l1_pre_topc(X1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_15,negated_conjecture,
% 1.73/1.00      ( v3_pre_topc(sK4,sK1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_366,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ r1_tarski(X0,X2)
% 1.73/1.00      | r1_tarski(X0,k1_tops_1(X1,X2))
% 1.73/1.00      | ~ l1_pre_topc(X1)
% 1.73/1.00      | sK4 != X0
% 1.73/1.00      | sK1 != X1 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_15]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_367,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ r1_tarski(sK4,X0)
% 1.73/1.00      | r1_tarski(sK4,k1_tops_1(sK1,X0))
% 1.73/1.00      | ~ l1_pre_topc(sK1) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_366]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_24,negated_conjecture,
% 1.73/1.00      ( l1_pre_topc(sK1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_18,negated_conjecture,
% 1.73/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.73/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_371,plain,
% 1.73/1.00      ( r1_tarski(sK4,k1_tops_1(sK1,X0))
% 1.73/1.00      | ~ r1_tarski(sK4,X0)
% 1.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_367,c_24,c_18]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_372,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ r1_tarski(sK4,X0)
% 1.73/1.00      | r1_tarski(sK4,k1_tops_1(sK1,X0)) ),
% 1.73/1.00      inference(renaming,[status(thm)],[c_371]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1670,plain,
% 1.73/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | r1_tarski(sK4,k1_tops_1(sK1,sK4))
% 1.73/1.00      | ~ r1_tarski(sK4,sK4) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_372]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2,plain,
% 1.73/1.00      ( r1_tarski(X0,X0) ),
% 1.73/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1669,plain,
% 1.73/1.00      ( r1_tarski(sK4,sK4) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_5,plain,
% 1.73/1.00      ( m1_connsp_2(X0,X1,X2)
% 1.73/1.00      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.73/1.00      | v2_struct_0(X1)
% 1.73/1.00      | ~ v2_pre_topc(X1)
% 1.73/1.00      | ~ l1_pre_topc(X1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_14,negated_conjecture,
% 1.73/1.00      ( r2_hidden(sK5,sK4) ),
% 1.73/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_392,plain,
% 1.73/1.00      ( m1_connsp_2(X0,X1,X2)
% 1.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.73/1.00      | v2_struct_0(X1)
% 1.73/1.00      | ~ v2_pre_topc(X1)
% 1.73/1.00      | ~ l1_pre_topc(X1)
% 1.73/1.00      | k1_tops_1(X1,X0) != sK4
% 1.73/1.00      | sK5 != X2 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_14]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_393,plain,
% 1.73/1.00      ( m1_connsp_2(X0,X1,sK5)
% 1.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ m1_subset_1(sK5,u1_struct_0(X1))
% 1.73/1.00      | v2_struct_0(X1)
% 1.73/1.00      | ~ v2_pre_topc(X1)
% 1.73/1.00      | ~ l1_pre_topc(X1)
% 1.73/1.00      | k1_tops_1(X1,X0) != sK4 ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_392]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_22,negated_conjecture,
% 1.73/1.00      ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 1.73/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_8,plain,
% 1.73/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 1.73/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.73/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.73/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 1.73/1.00      | ~ m1_pre_topc(X4,X0)
% 1.73/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.73/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.73/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.73/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.73/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.73/1.00      | ~ v1_funct_1(X2)
% 1.73/1.00      | v2_struct_0(X1)
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | v2_struct_0(X4)
% 1.73/1.00      | ~ v2_pre_topc(X1)
% 1.73/1.00      | ~ v2_pre_topc(X0)
% 1.73/1.00      | ~ l1_pre_topc(X1)
% 1.73/1.00      | ~ l1_pre_topc(X0) ),
% 1.73/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_19,negated_conjecture,
% 1.73/1.00      ( m1_pre_topc(sK3,sK1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_478,plain,
% 1.73/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 1.73/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.73/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.73/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 1.73/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.73/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.73/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.73/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.73/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.73/1.00      | ~ v1_funct_1(X2)
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | v2_struct_0(X1)
% 1.73/1.00      | v2_struct_0(X4)
% 1.73/1.00      | ~ v2_pre_topc(X0)
% 1.73/1.00      | ~ v2_pre_topc(X1)
% 1.73/1.00      | ~ l1_pre_topc(X0)
% 1.73/1.00      | ~ l1_pre_topc(X1)
% 1.73/1.00      | sK1 != X0
% 1.73/1.00      | sK3 != X4 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_479,plain,
% 1.73/1.00      ( r1_tmap_1(sK1,X0,X1,X2)
% 1.73/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.73/1.00      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
% 1.73/1.00      | ~ m1_connsp_2(X3,sK1,X2)
% 1.73/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.73/1.00      | ~ r1_tarski(X3,u1_struct_0(sK3))
% 1.73/1.00      | ~ v1_funct_1(X1)
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | v2_struct_0(sK1)
% 1.73/1.00      | v2_struct_0(sK3)
% 1.73/1.00      | ~ v2_pre_topc(X0)
% 1.73/1.00      | ~ v2_pre_topc(sK1)
% 1.73/1.00      | ~ l1_pre_topc(X0)
% 1.73/1.00      | ~ l1_pre_topc(sK1) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_478]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_26,negated_conjecture,
% 1.73/1.00      ( ~ v2_struct_0(sK1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_25,negated_conjecture,
% 1.73/1.00      ( v2_pre_topc(sK1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_20,negated_conjecture,
% 1.73/1.00      ( ~ v2_struct_0(sK3) ),
% 1.73/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_483,plain,
% 1.73/1.00      ( ~ l1_pre_topc(X0)
% 1.73/1.00      | r1_tmap_1(sK1,X0,X1,X2)
% 1.73/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.73/1.00      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
% 1.73/1.00      | ~ m1_connsp_2(X3,sK1,X2)
% 1.73/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.73/1.00      | ~ r1_tarski(X3,u1_struct_0(sK3))
% 1.73/1.00      | ~ v1_funct_1(X1)
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | ~ v2_pre_topc(X0) ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_479,c_26,c_25,c_24,c_20]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_484,plain,
% 1.73/1.00      ( r1_tmap_1(sK1,X0,X1,X2)
% 1.73/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.73/1.00      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
% 1.73/1.00      | ~ m1_connsp_2(X3,sK1,X2)
% 1.73/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.73/1.00      | ~ r1_tarski(X3,u1_struct_0(sK3))
% 1.73/1.00      | ~ v1_funct_1(X1)
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | ~ v2_pre_topc(X0)
% 1.73/1.00      | ~ l1_pre_topc(X0) ),
% 1.73/1.00      inference(renaming,[status(thm)],[c_483]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_531,plain,
% 1.73/1.00      ( r1_tmap_1(sK1,X0,X1,X2)
% 1.73/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.73/1.00      | ~ m1_connsp_2(X3,sK1,X2)
% 1.73/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.73/1.00      | ~ r1_tarski(X3,u1_struct_0(sK3))
% 1.73/1.00      | ~ v1_funct_1(X1)
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | ~ v2_pre_topc(X0)
% 1.73/1.00      | ~ l1_pre_topc(X0)
% 1.73/1.00      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.73/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.73/1.00      | sK2 != X1 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_484]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_532,plain,
% 1.73/1.00      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.73/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.73/1.00      | ~ m1_connsp_2(X2,sK1,X1)
% 1.73/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.73/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.73/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.00      | ~ r1_tarski(X2,u1_struct_0(sK3))
% 1.73/1.00      | ~ v1_funct_1(sK2)
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | ~ v2_pre_topc(X0)
% 1.73/1.00      | ~ l1_pre_topc(X0)
% 1.73/1.00      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_531]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_23,negated_conjecture,
% 1.73/1.00      ( v1_funct_1(sK2) ),
% 1.73/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_536,plain,
% 1.73/1.00      ( ~ r1_tarski(X2,u1_struct_0(sK3))
% 1.73/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.73/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.73/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_connsp_2(X2,sK1,X1)
% 1.73/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.73/1.00      | r1_tmap_1(sK1,X0,sK2,X1)
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | ~ v2_pre_topc(X0)
% 1.73/1.00      | ~ l1_pre_topc(X0)
% 1.73/1.00      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_532,c_23]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_537,plain,
% 1.73/1.00      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.73/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.73/1.00      | ~ m1_connsp_2(X2,sK1,X1)
% 1.73/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.73/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.73/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.00      | ~ r1_tarski(X2,u1_struct_0(sK3))
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | ~ v2_pre_topc(X0)
% 1.73/1.00      | ~ l1_pre_topc(X0)
% 1.73/1.00      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.73/1.00      inference(renaming,[status(thm)],[c_536]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_676,plain,
% 1.73/1.00      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.73/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.73/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.73/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.73/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.73/1.00      | ~ m1_subset_1(sK5,u1_struct_0(X3))
% 1.73/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.00      | ~ r1_tarski(X4,u1_struct_0(sK3))
% 1.73/1.00      | v2_struct_0(X3)
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | ~ v2_pre_topc(X3)
% 1.73/1.00      | ~ v2_pre_topc(X0)
% 1.73/1.00      | ~ l1_pre_topc(X3)
% 1.73/1.00      | ~ l1_pre_topc(X0)
% 1.73/1.00      | X4 != X2
% 1.73/1.00      | k1_tops_1(X3,X2) != sK4
% 1.73/1.00      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.73/1.00      | sK5 != X1
% 1.73/1.00      | sK1 != X3 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_393,c_537]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_677,plain,
% 1.73/1.00      ( r1_tmap_1(sK1,X0,sK2,sK5)
% 1.73/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
% 1.73/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
% 1.73/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.00      | ~ r1_tarski(X1,u1_struct_0(sK3))
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | v2_struct_0(sK1)
% 1.73/1.00      | ~ v2_pre_topc(X0)
% 1.73/1.00      | ~ v2_pre_topc(sK1)
% 1.73/1.00      | ~ l1_pre_topc(X0)
% 1.73/1.00      | ~ l1_pre_topc(sK1)
% 1.73/1.00      | k1_tops_1(sK1,X1) != sK4
% 1.73/1.00      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_676]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_17,negated_conjecture,
% 1.73/1.00      ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
% 1.73/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_681,plain,
% 1.73/1.00      ( ~ l1_pre_topc(X0)
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | ~ r1_tarski(X1,u1_struct_0(sK3))
% 1.73/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.00      | r1_tmap_1(sK1,X0,sK2,sK5)
% 1.73/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
% 1.73/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_pre_topc(X0)
% 1.73/1.00      | k1_tops_1(sK1,X1) != sK4
% 1.73/1.00      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_677,c_26,c_25,c_24,c_17]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_682,plain,
% 1.73/1.00      ( r1_tmap_1(sK1,X0,sK2,sK5)
% 1.73/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
% 1.73/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.00      | ~ r1_tarski(X1,u1_struct_0(sK3))
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | ~ v2_pre_topc(X0)
% 1.73/1.00      | ~ l1_pre_topc(X0)
% 1.73/1.00      | k1_tops_1(sK1,X1) != sK4
% 1.73/1.00      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.73/1.00      inference(renaming,[status(thm)],[c_681]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_28,negated_conjecture,
% 1.73/1.00      ( v2_pre_topc(sK0) ),
% 1.73/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_795,plain,
% 1.73/1.00      ( r1_tmap_1(sK1,X0,sK2,sK5)
% 1.73/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
% 1.73/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.00      | ~ r1_tarski(X1,u1_struct_0(sK3))
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | ~ l1_pre_topc(X0)
% 1.73/1.00      | k1_tops_1(sK1,X1) != sK4
% 1.73/1.00      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.73/1.00      | sK0 != X0 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_682,c_28]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_796,plain,
% 1.73/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.73/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.73/1.00      | ~ r1_tarski(X0,u1_struct_0(sK3))
% 1.73/1.00      | v2_struct_0(sK0)
% 1.73/1.00      | ~ l1_pre_topc(sK0)
% 1.73/1.00      | k1_tops_1(sK1,X0) != sK4
% 1.73/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_795]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_29,negated_conjecture,
% 1.73/1.00      ( ~ v2_struct_0(sK0) ),
% 1.73/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_27,negated_conjecture,
% 1.73/1.00      ( l1_pre_topc(sK0) ),
% 1.73/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_21,negated_conjecture,
% 1.73/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 1.73/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_800,plain,
% 1.73/1.00      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.73/1.00      | r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.73/1.00      | ~ r1_tarski(X0,u1_struct_0(sK3))
% 1.73/1.00      | k1_tops_1(sK1,X0) != sK4
% 1.73/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_796,c_29,c_27,c_21]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_801,plain,
% 1.73/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.73/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.00      | ~ r1_tarski(X0,u1_struct_0(sK3))
% 1.73/1.00      | k1_tops_1(sK1,X0) != sK4
% 1.73/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.73/1.00      inference(renaming,[status(thm)],[c_800]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_947,plain,
% 1.73/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.73/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.00      | ~ r1_tarski(X0,u1_struct_0(sK3))
% 1.73/1.00      | k1_tops_1(sK1,X0) != sK4 ),
% 1.73/1.00      inference(equality_resolution_simp,[status(thm)],[c_801]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1079,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ r1_tarski(X0,u1_struct_0(sK3))
% 1.73/1.00      | k1_tops_1(sK1,X0) != sK4
% 1.73/1.00      | ~ sP0_iProver_split ),
% 1.73/1.00      inference(splitting,
% 1.73/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.73/1.00                [c_947]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1666,plain,
% 1.73/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ r1_tarski(sK4,u1_struct_0(sK3))
% 1.73/1.00      | ~ sP0_iProver_split
% 1.73/1.00      | k1_tops_1(sK1,sK4) != sK4 ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_1079]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_3,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 1.73/1.00      | ~ l1_pre_topc(X1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_895,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 1.73/1.00      | sK1 != X1 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_896,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | r1_tarski(k1_tops_1(sK1,X0),X0) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_895]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1663,plain,
% 1.73/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | r1_tarski(k1_tops_1(sK1,sK4),sK4) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_896]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_9,plain,
% 1.73/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.73/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.73/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.73/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 1.73/1.00      | ~ m1_pre_topc(X4,X0)
% 1.73/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.73/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.73/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.73/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.73/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.73/1.00      | ~ v1_funct_1(X2)
% 1.73/1.00      | v2_struct_0(X1)
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | v2_struct_0(X4)
% 1.73/1.00      | ~ v2_pre_topc(X1)
% 1.73/1.00      | ~ v2_pre_topc(X0)
% 1.73/1.00      | ~ l1_pre_topc(X1)
% 1.73/1.00      | ~ l1_pre_topc(X0) ),
% 1.73/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_427,plain,
% 1.73/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.73/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.73/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.73/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 1.73/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.73/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.73/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.73/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.73/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.73/1.00      | ~ v1_funct_1(X2)
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | v2_struct_0(X1)
% 1.73/1.00      | v2_struct_0(X4)
% 1.73/1.00      | ~ v2_pre_topc(X0)
% 1.73/1.00      | ~ v2_pre_topc(X1)
% 1.73/1.00      | ~ l1_pre_topc(X0)
% 1.73/1.00      | ~ l1_pre_topc(X1)
% 1.73/1.00      | sK1 != X0
% 1.73/1.00      | sK3 != X4 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_428,plain,
% 1.73/1.00      ( ~ r1_tmap_1(sK1,X0,X1,X2)
% 1.73/1.00      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.73/1.00      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
% 1.73/1.00      | ~ m1_connsp_2(X3,sK1,X2)
% 1.73/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.73/1.00      | ~ r1_tarski(X3,u1_struct_0(sK3))
% 1.73/1.00      | ~ v1_funct_1(X1)
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | v2_struct_0(sK1)
% 1.73/1.00      | v2_struct_0(sK3)
% 1.73/1.00      | ~ v2_pre_topc(X0)
% 1.73/1.00      | ~ v2_pre_topc(sK1)
% 1.73/1.00      | ~ l1_pre_topc(X0)
% 1.73/1.00      | ~ l1_pre_topc(sK1) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_427]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_432,plain,
% 1.73/1.00      ( ~ l1_pre_topc(X0)
% 1.73/1.00      | ~ r1_tmap_1(sK1,X0,X1,X2)
% 1.73/1.00      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.73/1.00      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
% 1.73/1.00      | ~ m1_connsp_2(X3,sK1,X2)
% 1.73/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.73/1.00      | ~ r1_tarski(X3,u1_struct_0(sK3))
% 1.73/1.00      | ~ v1_funct_1(X1)
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | ~ v2_pre_topc(X0) ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_428,c_26,c_25,c_24,c_20]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_433,plain,
% 1.73/1.00      ( ~ r1_tmap_1(sK1,X0,X1,X2)
% 1.73/1.00      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.73/1.00      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
% 1.73/1.00      | ~ m1_connsp_2(X3,sK1,X2)
% 1.73/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.73/1.00      | ~ r1_tarski(X3,u1_struct_0(sK3))
% 1.73/1.00      | ~ v1_funct_1(X1)
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | ~ v2_pre_topc(X0)
% 1.73/1.00      | ~ l1_pre_topc(X0) ),
% 1.73/1.00      inference(renaming,[status(thm)],[c_432]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_579,plain,
% 1.73/1.00      ( ~ r1_tmap_1(sK1,X0,X1,X2)
% 1.73/1.00      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.73/1.00      | ~ m1_connsp_2(X3,sK1,X2)
% 1.73/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.73/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.73/1.00      | ~ r1_tarski(X3,u1_struct_0(sK3))
% 1.73/1.00      | ~ v1_funct_1(X1)
% 1.73/1.00      | v2_struct_0(X0)
% 1.73/1.00      | ~ v2_pre_topc(X0)
% 1.73/1.01      | ~ l1_pre_topc(X0)
% 1.73/1.01      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.73/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.73/1.01      | sK2 != X1 ),
% 1.73/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_433]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_580,plain,
% 1.73/1.01      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.73/1.01      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.73/1.01      | ~ m1_connsp_2(X2,sK1,X1)
% 1.73/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.73/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.73/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.01      | ~ r1_tarski(X2,u1_struct_0(sK3))
% 1.73/1.01      | ~ v1_funct_1(sK2)
% 1.73/1.01      | v2_struct_0(X0)
% 1.73/1.01      | ~ v2_pre_topc(X0)
% 1.73/1.01      | ~ l1_pre_topc(X0)
% 1.73/1.01      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.73/1.01      inference(unflattening,[status(thm)],[c_579]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_584,plain,
% 1.73/1.01      ( ~ r1_tarski(X2,u1_struct_0(sK3))
% 1.73/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.73/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.73/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.01      | ~ m1_connsp_2(X2,sK1,X1)
% 1.73/1.01      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.73/1.01      | ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.73/1.01      | v2_struct_0(X0)
% 1.73/1.01      | ~ v2_pre_topc(X0)
% 1.73/1.01      | ~ l1_pre_topc(X0)
% 1.73/1.01      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.73/1.01      inference(global_propositional_subsumption,
% 1.73/1.01                [status(thm)],
% 1.73/1.01                [c_580,c_23]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_585,plain,
% 1.73/1.01      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.73/1.01      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.73/1.01      | ~ m1_connsp_2(X2,sK1,X1)
% 1.73/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.73/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.73/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.01      | ~ r1_tarski(X2,u1_struct_0(sK3))
% 1.73/1.01      | v2_struct_0(X0)
% 1.73/1.01      | ~ v2_pre_topc(X0)
% 1.73/1.01      | ~ l1_pre_topc(X0)
% 1.73/1.01      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.73/1.01      inference(renaming,[status(thm)],[c_584]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_631,plain,
% 1.73/1.01      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.73/1.01      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.73/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.73/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.73/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.73/1.01      | ~ m1_subset_1(sK5,u1_struct_0(X3))
% 1.73/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.01      | ~ r1_tarski(X4,u1_struct_0(sK3))
% 1.73/1.01      | v2_struct_0(X3)
% 1.73/1.01      | v2_struct_0(X0)
% 1.73/1.01      | ~ v2_pre_topc(X3)
% 1.73/1.01      | ~ v2_pre_topc(X0)
% 1.73/1.01      | ~ l1_pre_topc(X3)
% 1.73/1.01      | ~ l1_pre_topc(X0)
% 1.73/1.01      | X4 != X2
% 1.73/1.01      | k1_tops_1(X3,X2) != sK4
% 1.73/1.01      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.73/1.01      | sK5 != X1
% 1.73/1.01      | sK1 != X3 ),
% 1.73/1.01      inference(resolution_lifted,[status(thm)],[c_393,c_585]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_632,plain,
% 1.73/1.01      ( ~ r1_tmap_1(sK1,X0,sK2,sK5)
% 1.73/1.01      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
% 1.73/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
% 1.73/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.01      | ~ r1_tarski(X1,u1_struct_0(sK3))
% 1.73/1.01      | v2_struct_0(X0)
% 1.73/1.01      | v2_struct_0(sK1)
% 1.73/1.01      | ~ v2_pre_topc(X0)
% 1.73/1.01      | ~ v2_pre_topc(sK1)
% 1.73/1.01      | ~ l1_pre_topc(X0)
% 1.73/1.01      | ~ l1_pre_topc(sK1)
% 1.73/1.01      | k1_tops_1(sK1,X1) != sK4
% 1.73/1.01      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.73/1.01      inference(unflattening,[status(thm)],[c_631]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_636,plain,
% 1.73/1.01      ( ~ l1_pre_topc(X0)
% 1.73/1.01      | v2_struct_0(X0)
% 1.73/1.01      | ~ r1_tarski(X1,u1_struct_0(sK3))
% 1.73/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.01      | ~ r1_tmap_1(sK1,X0,sK2,sK5)
% 1.73/1.01      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
% 1.73/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.01      | ~ v2_pre_topc(X0)
% 1.73/1.01      | k1_tops_1(sK1,X1) != sK4
% 1.73/1.01      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.73/1.01      inference(global_propositional_subsumption,
% 1.73/1.01                [status(thm)],
% 1.73/1.01                [c_632,c_26,c_25,c_24,c_17]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_637,plain,
% 1.73/1.01      ( ~ r1_tmap_1(sK1,X0,sK2,sK5)
% 1.73/1.01      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
% 1.73/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.01      | ~ r1_tarski(X1,u1_struct_0(sK3))
% 1.73/1.01      | v2_struct_0(X0)
% 1.73/1.01      | ~ v2_pre_topc(X0)
% 1.73/1.01      | ~ l1_pre_topc(X0)
% 1.73/1.01      | k1_tops_1(sK1,X1) != sK4
% 1.73/1.01      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.73/1.01      inference(renaming,[status(thm)],[c_636]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_828,plain,
% 1.73/1.01      ( ~ r1_tmap_1(sK1,X0,sK2,sK5)
% 1.73/1.01      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
% 1.73/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.73/1.01      | ~ r1_tarski(X1,u1_struct_0(sK3))
% 1.73/1.01      | v2_struct_0(X0)
% 1.73/1.01      | ~ l1_pre_topc(X0)
% 1.73/1.01      | k1_tops_1(sK1,X1) != sK4
% 1.73/1.01      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.73/1.01      | sK0 != X0 ),
% 1.73/1.01      inference(resolution_lifted,[status(thm)],[c_637,c_28]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_829,plain,
% 1.73/1.01      ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.73/1.01      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.73/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.73/1.01      | ~ r1_tarski(X0,u1_struct_0(sK3))
% 1.73/1.01      | v2_struct_0(sK0)
% 1.73/1.01      | ~ l1_pre_topc(sK0)
% 1.73/1.01      | k1_tops_1(sK1,X0) != sK4
% 1.73/1.01      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.73/1.01      inference(unflattening,[status(thm)],[c_828]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_833,plain,
% 1.73/1.01      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.01      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.73/1.01      | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.73/1.01      | ~ r1_tarski(X0,u1_struct_0(sK3))
% 1.73/1.01      | k1_tops_1(sK1,X0) != sK4
% 1.73/1.01      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.73/1.01      inference(global_propositional_subsumption,
% 1.73/1.01                [status(thm)],
% 1.73/1.01                [c_829,c_29,c_27,c_21]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_834,plain,
% 1.73/1.01      ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.73/1.01      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.73/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.01      | ~ r1_tarski(X0,u1_struct_0(sK3))
% 1.73/1.01      | k1_tops_1(sK1,X0) != sK4
% 1.73/1.01      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.73/1.01      inference(renaming,[status(thm)],[c_833]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_943,plain,
% 1.73/1.01      ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.73/1.01      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.73/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.01      | ~ r1_tarski(X0,u1_struct_0(sK3))
% 1.73/1.01      | k1_tops_1(sK1,X0) != sK4 ),
% 1.73/1.01      inference(equality_resolution_simp,[status(thm)],[c_834]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_1081,plain,
% 1.73/1.01      ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.73/1.01      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.73/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.01      | sP0_iProver_split ),
% 1.73/1.01      inference(splitting,
% 1.73/1.01                [splitting(split),new_symbols(definition,[])],
% 1.73/1.01                [c_943]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_1528,plain,
% 1.73/1.01      ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
% 1.73/1.01      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top
% 1.73/1.01      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 1.73/1.01      | sP0_iProver_split = iProver_top ),
% 1.73/1.01      inference(predicate_to_equality,[status(thm)],[c_1081]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_12,negated_conjecture,
% 1.73/1.01      ( sK5 = sK6 ),
% 1.73/1.01      inference(cnf_transformation,[],[f61]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_1607,plain,
% 1.73/1.01      ( r1_tmap_1(sK1,sK0,sK2,sK6) != iProver_top
% 1.73/1.01      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) = iProver_top
% 1.73/1.01      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 1.73/1.01      | sP0_iProver_split = iProver_top ),
% 1.73/1.01      inference(light_normalisation,[status(thm)],[c_1528,c_12]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_16,negated_conjecture,
% 1.73/1.01      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.73/1.01      inference(cnf_transformation,[],[f57]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_1540,plain,
% 1.73/1.01      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.73/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_1080,plain,
% 1.73/1.01      ( r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.73/1.01      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.73/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.73/1.01      | sP0_iProver_split ),
% 1.73/1.01      inference(splitting,
% 1.73/1.01                [splitting(split),new_symbols(definition,[])],
% 1.73/1.01                [c_947]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_1526,plain,
% 1.73/1.01      ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
% 1.73/1.01      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top
% 1.73/1.01      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 1.73/1.01      | sP0_iProver_split = iProver_top ),
% 1.73/1.01      inference(predicate_to_equality,[status(thm)],[c_1080]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_1599,plain,
% 1.73/1.01      ( r1_tmap_1(sK1,sK0,sK2,sK6) = iProver_top
% 1.73/1.01      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) != iProver_top
% 1.73/1.01      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 1.73/1.01      | sP0_iProver_split = iProver_top ),
% 1.73/1.01      inference(light_normalisation,[status(thm)],[c_1526,c_12]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_10,negated_conjecture,
% 1.73/1.01      ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.73/1.01      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) ),
% 1.73/1.01      inference(cnf_transformation,[],[f63]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_1543,plain,
% 1.73/1.01      ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
% 1.73/1.01      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) != iProver_top ),
% 1.73/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_1580,plain,
% 1.73/1.01      ( r1_tmap_1(sK1,sK0,sK2,sK6) != iProver_top
% 1.73/1.01      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) != iProver_top ),
% 1.73/1.01      inference(light_normalisation,[status(thm)],[c_1543,c_12]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_1604,plain,
% 1.73/1.01      ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) != iProver_top
% 1.73/1.01      | sP0_iProver_split = iProver_top ),
% 1.73/1.01      inference(forward_subsumption_resolution,
% 1.73/1.01                [status(thm)],
% 1.73/1.01                [c_1599,c_1540,c_1580]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_11,negated_conjecture,
% 1.73/1.01      ( r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.73/1.01      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) ),
% 1.73/1.01      inference(cnf_transformation,[],[f62]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_1542,plain,
% 1.73/1.01      ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
% 1.73/1.01      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) = iProver_top ),
% 1.73/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_1575,plain,
% 1.73/1.01      ( r1_tmap_1(sK1,sK0,sK2,sK6) = iProver_top
% 1.73/1.01      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) = iProver_top ),
% 1.73/1.01      inference(light_normalisation,[status(thm)],[c_1542,c_12]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_1612,plain,
% 1.73/1.01      ( sP0_iProver_split = iProver_top ),
% 1.73/1.01      inference(forward_subsumption_resolution,
% 1.73/1.01                [status(thm)],
% 1.73/1.01                [c_1607,c_1540,c_1604,c_1575]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_1621,plain,
% 1.73/1.01      ( sP0_iProver_split ),
% 1.73/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1612]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(c_13,negated_conjecture,
% 1.73/1.01      ( r1_tarski(sK4,u1_struct_0(sK3)) ),
% 1.73/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.73/1.01  
% 1.73/1.01  cnf(contradiction,plain,
% 1.73/1.01      ( $false ),
% 1.73/1.01      inference(minisat,
% 1.73/1.01                [status(thm)],
% 1.73/1.01                [c_1727,c_1670,c_1669,c_1666,c_1663,c_1621,c_13,c_18]) ).
% 1.73/1.01  
% 1.73/1.01  
% 1.73/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.73/1.01  
% 1.73/1.01  ------                               Statistics
% 1.73/1.01  
% 1.73/1.01  ------ General
% 1.73/1.01  
% 1.73/1.01  abstr_ref_over_cycles:                  0
% 1.73/1.01  abstr_ref_under_cycles:                 0
% 1.73/1.01  gc_basic_clause_elim:                   0
% 1.73/1.01  forced_gc_time:                         0
% 1.73/1.01  parsing_time:                           0.013
% 1.73/1.01  unif_index_cands_time:                  0.
% 1.73/1.01  unif_index_add_time:                    0.
% 1.73/1.01  orderings_time:                         0.
% 1.73/1.01  out_proof_time:                         0.018
% 1.73/1.01  total_time:                             0.1
% 1.73/1.01  num_of_symbols:                         56
% 1.73/1.01  num_of_terms:                           1010
% 1.73/1.01  
% 1.73/1.01  ------ Preprocessing
% 1.73/1.01  
% 1.73/1.01  num_of_splits:                          4
% 1.73/1.01  num_of_split_atoms:                     1
% 1.73/1.01  num_of_reused_defs:                     3
% 1.73/1.01  num_eq_ax_congr_red:                    7
% 1.73/1.01  num_of_sem_filtered_clauses:            1
% 1.73/1.01  num_of_subtypes:                        0
% 1.73/1.01  monotx_restored_types:                  0
% 1.73/1.01  sat_num_of_epr_types:                   0
% 1.73/1.01  sat_num_of_non_cyclic_types:            0
% 1.73/1.01  sat_guarded_non_collapsed_types:        0
% 1.73/1.01  num_pure_diseq_elim:                    0
% 1.73/1.01  simp_replaced_by:                       0
% 1.73/1.01  res_preprocessed:                       103
% 1.73/1.01  prep_upred:                             0
% 1.73/1.01  prep_unflattend:                        24
% 1.73/1.01  smt_new_axioms:                         0
% 1.73/1.01  pred_elim_cands:                        3
% 1.73/1.01  pred_elim:                              9
% 1.73/1.01  pred_elim_cl:                           12
% 1.73/1.01  pred_elim_cycles:                       11
% 1.73/1.01  merged_defs:                            8
% 1.73/1.01  merged_defs_ncl:                        0
% 1.73/1.01  bin_hyper_res:                          8
% 1.73/1.01  prep_cycles:                            4
% 1.73/1.01  pred_elim_time:                         0.02
% 1.73/1.01  splitting_time:                         0.
% 1.73/1.01  sem_filter_time:                        0.
% 1.73/1.01  monotx_time:                            0.
% 1.73/1.01  subtype_inf_time:                       0.
% 1.73/1.01  
% 1.73/1.01  ------ Problem properties
% 1.73/1.01  
% 1.73/1.01  clauses:                                21
% 1.73/1.01  conjectures:                            8
% 1.73/1.01  epr:                                    3
% 1.73/1.01  horn:                                   16
% 1.73/1.01  ground:                                 12
% 1.73/1.01  unary:                                  7
% 1.73/1.01  binary:                                 4
% 1.73/1.01  lits:                                   57
% 1.73/1.01  lits_eq:                                8
% 1.73/1.01  fd_pure:                                0
% 1.73/1.01  fd_pseudo:                              0
% 1.73/1.01  fd_cond:                                0
% 1.73/1.01  fd_pseudo_cond:                         1
% 1.73/1.01  ac_symbols:                             0
% 1.73/1.01  
% 1.73/1.01  ------ Propositional Solver
% 1.73/1.01  
% 1.73/1.01  prop_solver_calls:                      23
% 1.73/1.01  prop_fast_solver_calls:                 865
% 1.73/1.01  smt_solver_calls:                       0
% 1.73/1.01  smt_fast_solver_calls:                  0
% 1.73/1.01  prop_num_of_clauses:                    277
% 1.73/1.01  prop_preprocess_simplified:             2244
% 1.73/1.01  prop_fo_subsumed:                       31
% 1.73/1.01  prop_solver_time:                       0.
% 1.73/1.01  smt_solver_time:                        0.
% 1.73/1.01  smt_fast_solver_time:                   0.
% 1.73/1.01  prop_fast_solver_time:                  0.
% 1.73/1.01  prop_unsat_core_time:                   0.
% 1.73/1.01  
% 1.73/1.01  ------ QBF
% 1.73/1.01  
% 1.73/1.01  qbf_q_res:                              0
% 1.73/1.01  qbf_num_tautologies:                    0
% 1.73/1.01  qbf_prep_cycles:                        0
% 1.73/1.01  
% 1.73/1.01  ------ BMC1
% 1.73/1.01  
% 1.73/1.01  bmc1_current_bound:                     -1
% 1.73/1.01  bmc1_last_solved_bound:                 -1
% 1.73/1.01  bmc1_unsat_core_size:                   -1
% 1.73/1.01  bmc1_unsat_core_parents_size:           -1
% 1.73/1.01  bmc1_merge_next_fun:                    0
% 1.73/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.73/1.01  
% 1.73/1.01  ------ Instantiation
% 1.73/1.01  
% 1.73/1.01  inst_num_of_clauses:                    43
% 1.73/1.01  inst_num_in_passive:                    11
% 1.73/1.01  inst_num_in_active:                     30
% 1.73/1.01  inst_num_in_unprocessed:                1
% 1.73/1.01  inst_num_of_loops:                      32
% 1.73/1.01  inst_num_of_learning_restarts:          0
% 1.73/1.01  inst_num_moves_active_passive:          0
% 1.73/1.01  inst_lit_activity:                      0
% 1.73/1.01  inst_lit_activity_moves:                0
% 1.73/1.01  inst_num_tautologies:                   0
% 1.73/1.01  inst_num_prop_implied:                  0
% 1.73/1.01  inst_num_existing_simplified:           0
% 1.73/1.01  inst_num_eq_res_simplified:             0
% 1.73/1.01  inst_num_child_elim:                    0
% 1.73/1.01  inst_num_of_dismatching_blockings:      0
% 1.73/1.01  inst_num_of_non_proper_insts:           12
% 1.73/1.01  inst_num_of_duplicates:                 0
% 1.73/1.01  inst_inst_num_from_inst_to_res:         0
% 1.73/1.01  inst_dismatching_checking_time:         0.
% 1.73/1.01  
% 1.73/1.01  ------ Resolution
% 1.73/1.01  
% 1.73/1.01  res_num_of_clauses:                     0
% 1.73/1.01  res_num_in_passive:                     0
% 1.73/1.01  res_num_in_active:                      0
% 1.73/1.01  res_num_of_loops:                       107
% 1.73/1.01  res_forward_subset_subsumed:            0
% 1.73/1.01  res_backward_subset_subsumed:           0
% 1.73/1.01  res_forward_subsumed:                   0
% 1.73/1.01  res_backward_subsumed:                  0
% 1.73/1.01  res_forward_subsumption_resolution:     0
% 1.73/1.01  res_backward_subsumption_resolution:    0
% 1.73/1.01  res_clause_to_clause_subsumption:       83
% 1.73/1.01  res_orphan_elimination:                 0
% 1.73/1.01  res_tautology_del:                      18
% 1.73/1.01  res_num_eq_res_simplified:              2
% 1.73/1.01  res_num_sel_changes:                    0
% 1.73/1.01  res_moves_from_active_to_pass:          0
% 1.73/1.01  
% 1.73/1.01  ------ Superposition
% 1.73/1.01  
% 1.73/1.01  sup_time_total:                         0.
% 1.73/1.01  sup_time_generating:                    0.
% 1.73/1.01  sup_time_sim_full:                      0.
% 1.73/1.01  sup_time_sim_immed:                     0.
% 1.73/1.01  
% 1.73/1.01  sup_num_of_clauses:                     15
% 1.73/1.01  sup_num_in_active:                      6
% 1.73/1.01  sup_num_in_passive:                     9
% 1.73/1.01  sup_num_of_loops:                       6
% 1.73/1.01  sup_fw_superposition:                   0
% 1.73/1.01  sup_bw_superposition:                   0
% 1.73/1.01  sup_immediate_simplified:               0
% 1.73/1.01  sup_given_eliminated:                   0
% 1.73/1.01  comparisons_done:                       0
% 1.73/1.01  comparisons_avoided:                    0
% 1.73/1.01  
% 1.73/1.01  ------ Simplifications
% 1.73/1.01  
% 1.73/1.01  
% 1.73/1.01  sim_fw_subset_subsumed:                 2
% 1.73/1.01  sim_bw_subset_subsumed:                 0
% 1.73/1.01  sim_fw_subsumed:                        0
% 1.73/1.01  sim_bw_subsumed:                        1
% 1.73/1.01  sim_fw_subsumption_res:                 5
% 1.73/1.01  sim_bw_subsumption_res:                 1
% 1.73/1.01  sim_tautology_del:                      0
% 1.73/1.01  sim_eq_tautology_del:                   0
% 1.73/1.01  sim_eq_res_simp:                        0
% 1.73/1.01  sim_fw_demodulated:                     0
% 1.73/1.01  sim_bw_demodulated:                     0
% 1.73/1.01  sim_light_normalised:                   5
% 1.73/1.01  sim_joinable_taut:                      0
% 1.73/1.01  sim_joinable_simp:                      0
% 1.73/1.01  sim_ac_normalised:                      0
% 1.73/1.01  sim_smt_subsumption:                    0
% 1.73/1.01  
%------------------------------------------------------------------------------
