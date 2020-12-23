%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:39 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 810 expanded)
%              Number of clauses        :  105 ( 132 expanded)
%              Number of leaves         :   20 ( 355 expanded)
%              Depth                    :   26
%              Number of atoms          : 1406 (15761 expanded)
%              Number of equality atoms :  130 ( 995 expanded)
%              Maximal formula depth    :   27 (   9 average)
%              Maximal clause size      :   44 (   6 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f31,f38,f37,f36,f35,f34,f33,f32])).

fof(f64,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f29,plain,(
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

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
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
    inference(equality_resolution,[],[f53])).

fof(f61,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f56,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f55,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_connsp_2(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK0(X0,X1,X2),X2)
        & v3_pre_topc(sK0(X0,X1,X2),X0)
        & m1_connsp_2(sK0(X0,X1,X2),X0,X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(sK0(X0,X1,X2),X2)
                & v3_pre_topc(sK0(X0,X1,X2),X0)
                & m1_connsp_2(sK0(X0,X1,X2),X0,X1)
                & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f23])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK0(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK0(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f3])).

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
    inference(flattening,[],[f14])).

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
    inference(nnf_transformation,[],[f15])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK1(X0,X1,X2))
        & r1_tarski(sK1(X0,X1,X2),X2)
        & v3_pre_topc(sK1(X0,X1,X2),X0)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

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
                & ( ( r2_hidden(X1,sK1(X0,X1,X2))
                    & r1_tarski(sK1(X0,X1,X2),X2)
                    & v3_pre_topc(sK1(X0,X1,X2),X0)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f28])).

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
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,(
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
    inference(equality_resolution,[],[f51])).

fof(f71,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | ~ r1_tmap_1(sK3,sK2,sK4,sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | r1_tmap_1(sK3,sK2,sK4,sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    v3_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_12,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
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
    inference(cnf_transformation,[],[f75])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_550,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_26])).

cnf(c_551,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_550])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_555,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_connsp_2(X4,X2,X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_551,c_27])).

cnf(c_556,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_555])).

cnf(c_0,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_597,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_556,c_0])).

cnf(c_730,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_597])).

cnf(c_731,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_735,plain,
    ( ~ l1_pre_topc(X0)
    | r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_731,c_30,c_29,c_28,c_24])).

cnf(c_736,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_735])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1712,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_736,c_31])).

cnf(c_1713,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1712])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1717,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | r1_tmap_1(sK3,sK2,sK4,X0)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1713,c_33,c_32,c_25])).

cnf(c_1718,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1717])).

cnf(c_3133,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_54)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
    | ~ m1_connsp_2(X1_54,sK3,X0_54)
    | ~ r1_tarski(X1_54,u1_struct_0(sK5))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_1718])).

cnf(c_3360,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_54)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
    | ~ m1_connsp_2(X1_54,sK3,X0_54)
    | ~ r1_tarski(X1_54,u1_struct_0(sK5))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_3133])).

cnf(c_4975,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_54)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
    | ~ m1_connsp_2(sK0(sK3,sK7,u1_struct_0(sK5)),sK3,X0_54)
    | ~ r1_tarski(sK0(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3360])).

cnf(c_5699,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_connsp_2(sK0(sK3,sK7,u1_struct_0(sK5)),sK3,sK7)
    | ~ r1_tarski(sK0(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4975])).

cnf(c_3181,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,X0_54,X1_54)
    | r1_tmap_1(X0_53,X1_53,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_4477,plain,
    ( r1_tmap_1(sK5,sK2,X0_54,X1_54)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | X1_54 != sK7 ),
    inference(instantiation,[status(thm)],[c_3181])).

cnf(c_5078,plain,
    ( r1_tmap_1(sK5,sK2,X0_54,sK8)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK8 != sK7 ),
    inference(instantiation,[status(thm)],[c_4477])).

cnf(c_5563,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK8 != sK7 ),
    inference(instantiation,[status(thm)],[c_5078])).

cnf(c_3173,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_4525,plain,
    ( X0_54 != X1_54
    | X0_54 = sK7
    | sK7 != X1_54 ),
    inference(instantiation,[status(thm)],[c_3173])).

cnf(c_4721,plain,
    ( X0_54 = sK7
    | X0_54 != sK8
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_4525])).

cnf(c_4824,plain,
    ( sK7 != sK8
    | sK8 = sK7
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_4721])).

cnf(c_1,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_239,plain,
    ( r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1,c_0])).

cnf(c_240,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_239])).

cnf(c_1202,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_240,c_28])).

cnf(c_1203,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | r1_tarski(sK0(sK3,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1202])).

cnf(c_1207,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | r1_tarski(sK0(sK3,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1203,c_30,c_29])).

cnf(c_3155,plain,
    ( ~ m1_connsp_2(X0_54,sK3,X1_54)
    | r1_tarski(sK0(sK3,X1_54,X0_54),X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1207])).

cnf(c_4408,plain,
    ( ~ m1_connsp_2(X0_54,sK3,sK7)
    | r1_tarski(sK0(sK3,sK7,X0_54),X0_54)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3155])).

cnf(c_4790,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
    | r1_tarski(sK0(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4408])).

cnf(c_3,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_225,plain,
    ( m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_0])).

cnf(c_226,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_225])).

cnf(c_1244,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_226,c_28])).

cnf(c_1245,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | m1_connsp_2(sK0(sK3,X1,X0),sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1244])).

cnf(c_1249,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | m1_connsp_2(sK0(sK3,X1,X0),sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1245,c_30,c_29])).

cnf(c_3153,plain,
    ( ~ m1_connsp_2(X0_54,sK3,X1_54)
    | m1_connsp_2(sK0(sK3,X1_54,X0_54),sK3,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1249])).

cnf(c_4403,plain,
    ( ~ m1_connsp_2(X0_54,sK3,sK7)
    | m1_connsp_2(sK0(sK3,sK7,X0_54),sK3,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3153])).

cnf(c_4792,plain,
    ( m1_connsp_2(sK0(sK3,sK7,u1_struct_0(sK5)),sK3,sK7)
    | ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4403])).

cnf(c_3175,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | m1_subset_1(X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_4437,plain,
    ( m1_subset_1(X0_54,X1_54)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | X1_54 != u1_struct_0(sK5)
    | X0_54 != sK8 ),
    inference(instantiation,[status(thm)],[c_3175])).

cnf(c_4506,plain,
    ( m1_subset_1(sK7,X0_54)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | X0_54 != u1_struct_0(sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_4437])).

cnf(c_4757,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_4506])).

cnf(c_5,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,X3)
    | ~ v3_pre_topc(X3,X1)
    | ~ r1_tarski(X3,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1370,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,X3)
    | ~ v3_pre_topc(X3,X1)
    | ~ r1_tarski(X3,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_28])).

cnf(c_1371,plain,
    ( m1_connsp_2(X0,sK3,X1)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,sK3)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1370])).

cnf(c_1375,plain,
    ( m1_connsp_2(X0,sK3,X1)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,sK3)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1371,c_30,c_29])).

cnf(c_3147,plain,
    ( m1_connsp_2(X0_54,sK3,X1_54)
    | ~ r2_hidden(X1_54,X2_54)
    | ~ v3_pre_topc(X2_54,sK3)
    | ~ r1_tarski(X2_54,X0_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1375])).

cnf(c_4413,plain,
    ( m1_connsp_2(X0_54,sK3,X1_54)
    | ~ r2_hidden(X1_54,sK6)
    | ~ v3_pre_topc(sK6,sK3)
    | ~ r1_tarski(sK6,X0_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3147])).

cnf(c_4554,plain,
    ( m1_connsp_2(X0_54,sK3,sK7)
    | ~ r2_hidden(sK7,sK6)
    | ~ v3_pre_topc(sK6,sK3)
    | ~ r1_tarski(sK6,X0_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4413])).

cnf(c_4654,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
    | ~ r2_hidden(sK7,sK6)
    | ~ v3_pre_topc(sK6,sK3)
    | ~ r1_tarski(sK6,u1_struct_0(sK5))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4554])).

cnf(c_3172,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_4645,plain,
    ( k2_tmap_1(sK3,sK2,sK4,sK5) = k2_tmap_1(sK3,sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3172])).

cnf(c_4472,plain,
    ( r1_tmap_1(sK5,sK2,X0_54,X1_54)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | X1_54 != sK8 ),
    inference(instantiation,[status(thm)],[c_3181])).

cnf(c_4546,plain,
    ( r1_tmap_1(sK5,sK2,X0_54,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_4472])).

cnf(c_4644,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_4546])).

cnf(c_4571,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3172])).

cnf(c_4512,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_3172])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f74])).

cnf(c_618,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
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
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_619,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_623,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_619,c_27])).

cnf(c_624,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_623])).

cnf(c_688,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_624])).

cnf(c_689,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_693,plain,
    ( ~ l1_pre_topc(X0)
    | ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_689,c_30,c_29,c_28,c_24])).

cnf(c_694,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_693])).

cnf(c_1745,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_694,c_31])).

cnf(c_1746,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1745])).

cnf(c_1750,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1746,c_33,c_32,c_25])).

cnf(c_1751,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1750])).

cnf(c_3132,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0_54)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_1751])).

cnf(c_3364,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0_54)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_3132])).

cnf(c_4418,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3364])).

cnf(c_16,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3164,negated_conjecture,
    ( sK7 = sK8 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_677,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_678,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_15,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_19,negated_conjecture,
    ( v3_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5699,c_5563,c_4824,c_4790,c_4792,c_4757,c_4654,c_4645,c_4644,c_4571,c_4512,c_4418,c_3164,c_678,c_14,c_15,c_17,c_18,c_19,c_20,c_21,c_22,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:48:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.23/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.03  
% 2.23/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.23/1.03  
% 2.23/1.03  ------  iProver source info
% 2.23/1.03  
% 2.23/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.23/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.23/1.03  git: non_committed_changes: false
% 2.23/1.03  git: last_make_outside_of_git: false
% 2.23/1.03  
% 2.23/1.03  ------ 
% 2.23/1.03  
% 2.23/1.03  ------ Input Options
% 2.23/1.03  
% 2.23/1.03  --out_options                           all
% 2.23/1.03  --tptp_safe_out                         true
% 2.23/1.03  --problem_path                          ""
% 2.23/1.03  --include_path                          ""
% 2.23/1.03  --clausifier                            res/vclausify_rel
% 2.23/1.03  --clausifier_options                    --mode clausify
% 2.23/1.03  --stdin                                 false
% 2.23/1.03  --stats_out                             all
% 2.23/1.03  
% 2.23/1.03  ------ General Options
% 2.23/1.03  
% 2.23/1.03  --fof                                   false
% 2.23/1.03  --time_out_real                         305.
% 2.23/1.03  --time_out_virtual                      -1.
% 2.23/1.03  --symbol_type_check                     false
% 2.23/1.03  --clausify_out                          false
% 2.23/1.03  --sig_cnt_out                           false
% 2.23/1.03  --trig_cnt_out                          false
% 2.23/1.03  --trig_cnt_out_tolerance                1.
% 2.23/1.03  --trig_cnt_out_sk_spl                   false
% 2.23/1.03  --abstr_cl_out                          false
% 2.23/1.03  
% 2.23/1.03  ------ Global Options
% 2.23/1.03  
% 2.23/1.03  --schedule                              default
% 2.23/1.03  --add_important_lit                     false
% 2.23/1.03  --prop_solver_per_cl                    1000
% 2.23/1.03  --min_unsat_core                        false
% 2.23/1.03  --soft_assumptions                      false
% 2.23/1.03  --soft_lemma_size                       3
% 2.23/1.03  --prop_impl_unit_size                   0
% 2.23/1.03  --prop_impl_unit                        []
% 2.23/1.03  --share_sel_clauses                     true
% 2.23/1.03  --reset_solvers                         false
% 2.23/1.03  --bc_imp_inh                            [conj_cone]
% 2.23/1.03  --conj_cone_tolerance                   3.
% 2.23/1.03  --extra_neg_conj                        none
% 2.23/1.03  --large_theory_mode                     true
% 2.23/1.03  --prolific_symb_bound                   200
% 2.23/1.03  --lt_threshold                          2000
% 2.23/1.03  --clause_weak_htbl                      true
% 2.23/1.03  --gc_record_bc_elim                     false
% 2.23/1.03  
% 2.23/1.03  ------ Preprocessing Options
% 2.23/1.03  
% 2.23/1.03  --preprocessing_flag                    true
% 2.23/1.03  --time_out_prep_mult                    0.1
% 2.23/1.03  --splitting_mode                        input
% 2.23/1.03  --splitting_grd                         true
% 2.23/1.03  --splitting_cvd                         false
% 2.23/1.03  --splitting_cvd_svl                     false
% 2.23/1.03  --splitting_nvd                         32
% 2.23/1.03  --sub_typing                            true
% 2.23/1.03  --prep_gs_sim                           true
% 2.23/1.03  --prep_unflatten                        true
% 2.23/1.03  --prep_res_sim                          true
% 2.23/1.03  --prep_upred                            true
% 2.23/1.03  --prep_sem_filter                       exhaustive
% 2.23/1.03  --prep_sem_filter_out                   false
% 2.23/1.03  --pred_elim                             true
% 2.23/1.03  --res_sim_input                         true
% 2.23/1.03  --eq_ax_congr_red                       true
% 2.23/1.03  --pure_diseq_elim                       true
% 2.23/1.03  --brand_transform                       false
% 2.23/1.03  --non_eq_to_eq                          false
% 2.23/1.03  --prep_def_merge                        true
% 2.23/1.03  --prep_def_merge_prop_impl              false
% 2.23/1.03  --prep_def_merge_mbd                    true
% 2.23/1.03  --prep_def_merge_tr_red                 false
% 2.23/1.03  --prep_def_merge_tr_cl                  false
% 2.23/1.03  --smt_preprocessing                     true
% 2.23/1.03  --smt_ac_axioms                         fast
% 2.23/1.03  --preprocessed_out                      false
% 2.23/1.03  --preprocessed_stats                    false
% 2.23/1.03  
% 2.23/1.03  ------ Abstraction refinement Options
% 2.23/1.03  
% 2.23/1.03  --abstr_ref                             []
% 2.23/1.03  --abstr_ref_prep                        false
% 2.23/1.03  --abstr_ref_until_sat                   false
% 2.23/1.03  --abstr_ref_sig_restrict                funpre
% 2.23/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.23/1.03  --abstr_ref_under                       []
% 2.23/1.03  
% 2.23/1.03  ------ SAT Options
% 2.23/1.03  
% 2.23/1.03  --sat_mode                              false
% 2.23/1.03  --sat_fm_restart_options                ""
% 2.23/1.03  --sat_gr_def                            false
% 2.23/1.03  --sat_epr_types                         true
% 2.23/1.03  --sat_non_cyclic_types                  false
% 2.23/1.03  --sat_finite_models                     false
% 2.23/1.03  --sat_fm_lemmas                         false
% 2.23/1.03  --sat_fm_prep                           false
% 2.23/1.03  --sat_fm_uc_incr                        true
% 2.23/1.03  --sat_out_model                         small
% 2.23/1.03  --sat_out_clauses                       false
% 2.23/1.03  
% 2.23/1.03  ------ QBF Options
% 2.23/1.03  
% 2.23/1.03  --qbf_mode                              false
% 2.23/1.03  --qbf_elim_univ                         false
% 2.23/1.03  --qbf_dom_inst                          none
% 2.23/1.03  --qbf_dom_pre_inst                      false
% 2.23/1.03  --qbf_sk_in                             false
% 2.23/1.03  --qbf_pred_elim                         true
% 2.23/1.03  --qbf_split                             512
% 2.23/1.03  
% 2.23/1.03  ------ BMC1 Options
% 2.23/1.03  
% 2.23/1.03  --bmc1_incremental                      false
% 2.23/1.03  --bmc1_axioms                           reachable_all
% 2.23/1.03  --bmc1_min_bound                        0
% 2.23/1.03  --bmc1_max_bound                        -1
% 2.23/1.03  --bmc1_max_bound_default                -1
% 2.23/1.03  --bmc1_symbol_reachability              true
% 2.23/1.03  --bmc1_property_lemmas                  false
% 2.23/1.03  --bmc1_k_induction                      false
% 2.23/1.03  --bmc1_non_equiv_states                 false
% 2.23/1.03  --bmc1_deadlock                         false
% 2.23/1.03  --bmc1_ucm                              false
% 2.23/1.03  --bmc1_add_unsat_core                   none
% 2.23/1.03  --bmc1_unsat_core_children              false
% 2.23/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.23/1.03  --bmc1_out_stat                         full
% 2.23/1.03  --bmc1_ground_init                      false
% 2.23/1.03  --bmc1_pre_inst_next_state              false
% 2.23/1.03  --bmc1_pre_inst_state                   false
% 2.23/1.03  --bmc1_pre_inst_reach_state             false
% 2.23/1.03  --bmc1_out_unsat_core                   false
% 2.23/1.03  --bmc1_aig_witness_out                  false
% 2.23/1.03  --bmc1_verbose                          false
% 2.23/1.03  --bmc1_dump_clauses_tptp                false
% 2.23/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.23/1.03  --bmc1_dump_file                        -
% 2.23/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.23/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.23/1.03  --bmc1_ucm_extend_mode                  1
% 2.23/1.03  --bmc1_ucm_init_mode                    2
% 2.23/1.03  --bmc1_ucm_cone_mode                    none
% 2.23/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.23/1.03  --bmc1_ucm_relax_model                  4
% 2.23/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.23/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.23/1.03  --bmc1_ucm_layered_model                none
% 2.23/1.03  --bmc1_ucm_max_lemma_size               10
% 2.23/1.03  
% 2.23/1.03  ------ AIG Options
% 2.23/1.03  
% 2.23/1.03  --aig_mode                              false
% 2.23/1.03  
% 2.23/1.03  ------ Instantiation Options
% 2.23/1.03  
% 2.23/1.03  --instantiation_flag                    true
% 2.23/1.03  --inst_sos_flag                         false
% 2.23/1.03  --inst_sos_phase                        true
% 2.23/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.23/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.23/1.03  --inst_lit_sel_side                     num_symb
% 2.23/1.03  --inst_solver_per_active                1400
% 2.23/1.03  --inst_solver_calls_frac                1.
% 2.23/1.03  --inst_passive_queue_type               priority_queues
% 2.23/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.23/1.03  --inst_passive_queues_freq              [25;2]
% 2.23/1.03  --inst_dismatching                      true
% 2.23/1.03  --inst_eager_unprocessed_to_passive     true
% 2.23/1.03  --inst_prop_sim_given                   true
% 2.23/1.03  --inst_prop_sim_new                     false
% 2.23/1.03  --inst_subs_new                         false
% 2.23/1.03  --inst_eq_res_simp                      false
% 2.23/1.03  --inst_subs_given                       false
% 2.23/1.03  --inst_orphan_elimination               true
% 2.23/1.03  --inst_learning_loop_flag               true
% 2.23/1.03  --inst_learning_start                   3000
% 2.23/1.03  --inst_learning_factor                  2
% 2.23/1.03  --inst_start_prop_sim_after_learn       3
% 2.23/1.03  --inst_sel_renew                        solver
% 2.23/1.03  --inst_lit_activity_flag                true
% 2.23/1.03  --inst_restr_to_given                   false
% 2.23/1.03  --inst_activity_threshold               500
% 2.23/1.03  --inst_out_proof                        true
% 2.23/1.03  
% 2.23/1.03  ------ Resolution Options
% 2.23/1.03  
% 2.23/1.03  --resolution_flag                       true
% 2.23/1.03  --res_lit_sel                           adaptive
% 2.23/1.03  --res_lit_sel_side                      none
% 2.23/1.03  --res_ordering                          kbo
% 2.23/1.03  --res_to_prop_solver                    active
% 2.23/1.03  --res_prop_simpl_new                    false
% 2.23/1.03  --res_prop_simpl_given                  true
% 2.23/1.03  --res_passive_queue_type                priority_queues
% 2.23/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.23/1.03  --res_passive_queues_freq               [15;5]
% 2.23/1.03  --res_forward_subs                      full
% 2.23/1.03  --res_backward_subs                     full
% 2.23/1.03  --res_forward_subs_resolution           true
% 2.23/1.03  --res_backward_subs_resolution          true
% 2.23/1.03  --res_orphan_elimination                true
% 2.23/1.03  --res_time_limit                        2.
% 2.23/1.03  --res_out_proof                         true
% 2.23/1.03  
% 2.23/1.03  ------ Superposition Options
% 2.23/1.03  
% 2.23/1.03  --superposition_flag                    true
% 2.23/1.03  --sup_passive_queue_type                priority_queues
% 2.23/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.23/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.23/1.03  --demod_completeness_check              fast
% 2.23/1.03  --demod_use_ground                      true
% 2.23/1.03  --sup_to_prop_solver                    passive
% 2.23/1.03  --sup_prop_simpl_new                    true
% 2.23/1.03  --sup_prop_simpl_given                  true
% 2.23/1.03  --sup_fun_splitting                     false
% 2.23/1.03  --sup_smt_interval                      50000
% 2.23/1.03  
% 2.23/1.03  ------ Superposition Simplification Setup
% 2.23/1.03  
% 2.23/1.03  --sup_indices_passive                   []
% 2.23/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.23/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.03  --sup_full_bw                           [BwDemod]
% 2.23/1.03  --sup_immed_triv                        [TrivRules]
% 2.23/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.23/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.03  --sup_immed_bw_main                     []
% 2.23/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.23/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/1.03  
% 2.23/1.03  ------ Combination Options
% 2.23/1.03  
% 2.23/1.03  --comb_res_mult                         3
% 2.23/1.03  --comb_sup_mult                         2
% 2.23/1.03  --comb_inst_mult                        10
% 2.23/1.03  
% 2.23/1.03  ------ Debug Options
% 2.23/1.03  
% 2.23/1.03  --dbg_backtrace                         false
% 2.23/1.03  --dbg_dump_prop_clauses                 false
% 2.23/1.03  --dbg_dump_prop_clauses_file            -
% 2.23/1.03  --dbg_out_stat                          false
% 2.23/1.03  ------ Parsing...
% 2.23/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.23/1.03  
% 2.23/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 2.23/1.03  
% 2.23/1.03  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.23/1.03  
% 2.23/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.23/1.03  ------ Proving...
% 2.23/1.03  ------ Problem Properties 
% 2.23/1.03  
% 2.23/1.03  
% 2.23/1.03  clauses                                 37
% 2.23/1.03  conjectures                             10
% 2.23/1.03  EPR                                     3
% 2.23/1.03  Horn                                    36
% 2.23/1.03  unary                                   9
% 2.23/1.03  binary                                  2
% 2.23/1.03  lits                                    111
% 2.23/1.03  lits eq                                 5
% 2.23/1.03  fd_pure                                 0
% 2.23/1.03  fd_pseudo                               0
% 2.23/1.03  fd_cond                                 0
% 2.23/1.03  fd_pseudo_cond                          0
% 2.23/1.03  AC symbols                              0
% 2.23/1.03  
% 2.23/1.03  ------ Schedule dynamic 5 is on 
% 2.23/1.03  
% 2.23/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.23/1.03  
% 2.23/1.03  
% 2.23/1.03  ------ 
% 2.23/1.03  Current options:
% 2.23/1.03  ------ 
% 2.23/1.03  
% 2.23/1.03  ------ Input Options
% 2.23/1.03  
% 2.23/1.03  --out_options                           all
% 2.23/1.03  --tptp_safe_out                         true
% 2.23/1.03  --problem_path                          ""
% 2.23/1.03  --include_path                          ""
% 2.23/1.03  --clausifier                            res/vclausify_rel
% 2.23/1.03  --clausifier_options                    --mode clausify
% 2.23/1.03  --stdin                                 false
% 2.23/1.03  --stats_out                             all
% 2.23/1.03  
% 2.23/1.03  ------ General Options
% 2.23/1.03  
% 2.23/1.03  --fof                                   false
% 2.23/1.03  --time_out_real                         305.
% 2.23/1.03  --time_out_virtual                      -1.
% 2.23/1.03  --symbol_type_check                     false
% 2.23/1.03  --clausify_out                          false
% 2.23/1.03  --sig_cnt_out                           false
% 2.23/1.03  --trig_cnt_out                          false
% 2.23/1.03  --trig_cnt_out_tolerance                1.
% 2.23/1.03  --trig_cnt_out_sk_spl                   false
% 2.23/1.03  --abstr_cl_out                          false
% 2.23/1.03  
% 2.23/1.03  ------ Global Options
% 2.23/1.03  
% 2.23/1.03  --schedule                              default
% 2.23/1.03  --add_important_lit                     false
% 2.23/1.03  --prop_solver_per_cl                    1000
% 2.23/1.03  --min_unsat_core                        false
% 2.23/1.03  --soft_assumptions                      false
% 2.23/1.03  --soft_lemma_size                       3
% 2.23/1.03  --prop_impl_unit_size                   0
% 2.23/1.03  --prop_impl_unit                        []
% 2.23/1.03  --share_sel_clauses                     true
% 2.23/1.03  --reset_solvers                         false
% 2.23/1.03  --bc_imp_inh                            [conj_cone]
% 2.23/1.03  --conj_cone_tolerance                   3.
% 2.23/1.03  --extra_neg_conj                        none
% 2.23/1.03  --large_theory_mode                     true
% 2.23/1.03  --prolific_symb_bound                   200
% 2.23/1.03  --lt_threshold                          2000
% 2.23/1.03  --clause_weak_htbl                      true
% 2.23/1.03  --gc_record_bc_elim                     false
% 2.23/1.03  
% 2.23/1.03  ------ Preprocessing Options
% 2.23/1.03  
% 2.23/1.03  --preprocessing_flag                    true
% 2.23/1.03  --time_out_prep_mult                    0.1
% 2.23/1.03  --splitting_mode                        input
% 2.23/1.03  --splitting_grd                         true
% 2.23/1.03  --splitting_cvd                         false
% 2.23/1.03  --splitting_cvd_svl                     false
% 2.23/1.03  --splitting_nvd                         32
% 2.23/1.03  --sub_typing                            true
% 2.23/1.03  --prep_gs_sim                           true
% 2.23/1.03  --prep_unflatten                        true
% 2.23/1.03  --prep_res_sim                          true
% 2.23/1.03  --prep_upred                            true
% 2.23/1.03  --prep_sem_filter                       exhaustive
% 2.23/1.03  --prep_sem_filter_out                   false
% 2.23/1.03  --pred_elim                             true
% 2.23/1.03  --res_sim_input                         true
% 2.23/1.03  --eq_ax_congr_red                       true
% 2.23/1.03  --pure_diseq_elim                       true
% 2.23/1.03  --brand_transform                       false
% 2.23/1.03  --non_eq_to_eq                          false
% 2.23/1.03  --prep_def_merge                        true
% 2.23/1.03  --prep_def_merge_prop_impl              false
% 2.23/1.03  --prep_def_merge_mbd                    true
% 2.23/1.03  --prep_def_merge_tr_red                 false
% 2.23/1.03  --prep_def_merge_tr_cl                  false
% 2.23/1.03  --smt_preprocessing                     true
% 2.23/1.03  --smt_ac_axioms                         fast
% 2.23/1.03  --preprocessed_out                      false
% 2.23/1.03  --preprocessed_stats                    false
% 2.23/1.03  
% 2.23/1.03  ------ Abstraction refinement Options
% 2.23/1.03  
% 2.23/1.03  --abstr_ref                             []
% 2.23/1.03  --abstr_ref_prep                        false
% 2.23/1.03  --abstr_ref_until_sat                   false
% 2.23/1.03  --abstr_ref_sig_restrict                funpre
% 2.23/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.23/1.03  --abstr_ref_under                       []
% 2.23/1.03  
% 2.23/1.03  ------ SAT Options
% 2.23/1.03  
% 2.23/1.03  --sat_mode                              false
% 2.23/1.03  --sat_fm_restart_options                ""
% 2.23/1.03  --sat_gr_def                            false
% 2.23/1.03  --sat_epr_types                         true
% 2.23/1.03  --sat_non_cyclic_types                  false
% 2.23/1.03  --sat_finite_models                     false
% 2.23/1.03  --sat_fm_lemmas                         false
% 2.23/1.03  --sat_fm_prep                           false
% 2.23/1.03  --sat_fm_uc_incr                        true
% 2.23/1.03  --sat_out_model                         small
% 2.23/1.03  --sat_out_clauses                       false
% 2.23/1.03  
% 2.23/1.03  ------ QBF Options
% 2.23/1.03  
% 2.23/1.03  --qbf_mode                              false
% 2.23/1.03  --qbf_elim_univ                         false
% 2.23/1.03  --qbf_dom_inst                          none
% 2.23/1.03  --qbf_dom_pre_inst                      false
% 2.23/1.03  --qbf_sk_in                             false
% 2.23/1.03  --qbf_pred_elim                         true
% 2.23/1.03  --qbf_split                             512
% 2.23/1.03  
% 2.23/1.03  ------ BMC1 Options
% 2.23/1.03  
% 2.23/1.03  --bmc1_incremental                      false
% 2.23/1.03  --bmc1_axioms                           reachable_all
% 2.23/1.03  --bmc1_min_bound                        0
% 2.23/1.03  --bmc1_max_bound                        -1
% 2.23/1.03  --bmc1_max_bound_default                -1
% 2.23/1.03  --bmc1_symbol_reachability              true
% 2.23/1.03  --bmc1_property_lemmas                  false
% 2.23/1.03  --bmc1_k_induction                      false
% 2.23/1.03  --bmc1_non_equiv_states                 false
% 2.23/1.03  --bmc1_deadlock                         false
% 2.23/1.03  --bmc1_ucm                              false
% 2.23/1.03  --bmc1_add_unsat_core                   none
% 2.23/1.03  --bmc1_unsat_core_children              false
% 2.23/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.23/1.03  --bmc1_out_stat                         full
% 2.23/1.03  --bmc1_ground_init                      false
% 2.23/1.03  --bmc1_pre_inst_next_state              false
% 2.23/1.03  --bmc1_pre_inst_state                   false
% 2.23/1.03  --bmc1_pre_inst_reach_state             false
% 2.23/1.03  --bmc1_out_unsat_core                   false
% 2.23/1.03  --bmc1_aig_witness_out                  false
% 2.23/1.03  --bmc1_verbose                          false
% 2.23/1.03  --bmc1_dump_clauses_tptp                false
% 2.23/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.23/1.03  --bmc1_dump_file                        -
% 2.23/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.23/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.23/1.03  --bmc1_ucm_extend_mode                  1
% 2.23/1.03  --bmc1_ucm_init_mode                    2
% 2.23/1.03  --bmc1_ucm_cone_mode                    none
% 2.23/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.23/1.03  --bmc1_ucm_relax_model                  4
% 2.23/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.23/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.23/1.03  --bmc1_ucm_layered_model                none
% 2.23/1.03  --bmc1_ucm_max_lemma_size               10
% 2.23/1.03  
% 2.23/1.03  ------ AIG Options
% 2.23/1.03  
% 2.23/1.03  --aig_mode                              false
% 2.23/1.03  
% 2.23/1.03  ------ Instantiation Options
% 2.23/1.03  
% 2.23/1.03  --instantiation_flag                    true
% 2.23/1.03  --inst_sos_flag                         false
% 2.23/1.03  --inst_sos_phase                        true
% 2.23/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.23/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.23/1.03  --inst_lit_sel_side                     none
% 2.23/1.03  --inst_solver_per_active                1400
% 2.23/1.03  --inst_solver_calls_frac                1.
% 2.23/1.03  --inst_passive_queue_type               priority_queues
% 2.23/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.23/1.03  --inst_passive_queues_freq              [25;2]
% 2.23/1.03  --inst_dismatching                      true
% 2.23/1.03  --inst_eager_unprocessed_to_passive     true
% 2.23/1.03  --inst_prop_sim_given                   true
% 2.23/1.03  --inst_prop_sim_new                     false
% 2.23/1.03  --inst_subs_new                         false
% 2.23/1.03  --inst_eq_res_simp                      false
% 2.23/1.03  --inst_subs_given                       false
% 2.23/1.03  --inst_orphan_elimination               true
% 2.23/1.03  --inst_learning_loop_flag               true
% 2.23/1.03  --inst_learning_start                   3000
% 2.23/1.03  --inst_learning_factor                  2
% 2.23/1.03  --inst_start_prop_sim_after_learn       3
% 2.23/1.03  --inst_sel_renew                        solver
% 2.23/1.03  --inst_lit_activity_flag                true
% 2.23/1.03  --inst_restr_to_given                   false
% 2.23/1.03  --inst_activity_threshold               500
% 2.23/1.03  --inst_out_proof                        true
% 2.23/1.03  
% 2.23/1.03  ------ Resolution Options
% 2.23/1.03  
% 2.23/1.03  --resolution_flag                       false
% 2.23/1.03  --res_lit_sel                           adaptive
% 2.23/1.03  --res_lit_sel_side                      none
% 2.23/1.03  --res_ordering                          kbo
% 2.23/1.03  --res_to_prop_solver                    active
% 2.23/1.03  --res_prop_simpl_new                    false
% 2.23/1.03  --res_prop_simpl_given                  true
% 2.23/1.03  --res_passive_queue_type                priority_queues
% 2.23/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.23/1.03  --res_passive_queues_freq               [15;5]
% 2.23/1.03  --res_forward_subs                      full
% 2.23/1.03  --res_backward_subs                     full
% 2.23/1.03  --res_forward_subs_resolution           true
% 2.23/1.03  --res_backward_subs_resolution          true
% 2.23/1.03  --res_orphan_elimination                true
% 2.23/1.03  --res_time_limit                        2.
% 2.23/1.03  --res_out_proof                         true
% 2.23/1.03  
% 2.23/1.03  ------ Superposition Options
% 2.23/1.03  
% 2.23/1.03  --superposition_flag                    true
% 2.23/1.03  --sup_passive_queue_type                priority_queues
% 2.23/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.23/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.23/1.03  --demod_completeness_check              fast
% 2.23/1.03  --demod_use_ground                      true
% 2.23/1.03  --sup_to_prop_solver                    passive
% 2.23/1.03  --sup_prop_simpl_new                    true
% 2.23/1.03  --sup_prop_simpl_given                  true
% 2.23/1.03  --sup_fun_splitting                     false
% 2.23/1.03  --sup_smt_interval                      50000
% 2.23/1.03  
% 2.23/1.03  ------ Superposition Simplification Setup
% 2.23/1.03  
% 2.23/1.03  --sup_indices_passive                   []
% 2.23/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.23/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.03  --sup_full_bw                           [BwDemod]
% 2.23/1.03  --sup_immed_triv                        [TrivRules]
% 2.23/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.23/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.03  --sup_immed_bw_main                     []
% 2.23/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.23/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/1.03  
% 2.23/1.03  ------ Combination Options
% 2.23/1.03  
% 2.23/1.03  --comb_res_mult                         3
% 2.23/1.03  --comb_sup_mult                         2
% 2.23/1.03  --comb_inst_mult                        10
% 2.23/1.03  
% 2.23/1.03  ------ Debug Options
% 2.23/1.03  
% 2.23/1.03  --dbg_backtrace                         false
% 2.23/1.03  --dbg_dump_prop_clauses                 false
% 2.23/1.03  --dbg_dump_prop_clauses_file            -
% 2.23/1.03  --dbg_out_stat                          false
% 2.23/1.03  
% 2.23/1.03  
% 2.23/1.03  
% 2.23/1.03  
% 2.23/1.03  ------ Proving...
% 2.23/1.03  
% 2.23/1.03  
% 2.23/1.03  % SZS status Theorem for theBenchmark.p
% 2.23/1.03  
% 2.23/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.23/1.03  
% 2.23/1.03  fof(f7,conjecture,(
% 2.23/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.23/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.03  
% 2.23/1.03  fof(f8,negated_conjecture,(
% 2.23/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.23/1.03    inference(negated_conjecture,[],[f7])).
% 2.23/1.03  
% 2.23/1.03  fof(f21,plain,(
% 2.23/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.23/1.03    inference(ennf_transformation,[],[f8])).
% 2.23/1.03  
% 2.23/1.03  fof(f22,plain,(
% 2.23/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.23/1.03    inference(flattening,[],[f21])).
% 2.23/1.03  
% 2.23/1.03  fof(f30,plain,(
% 2.23/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5))) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.23/1.03    inference(nnf_transformation,[],[f22])).
% 2.23/1.03  
% 2.23/1.03  fof(f31,plain,(
% 2.23/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.23/1.03    inference(flattening,[],[f30])).
% 2.23/1.03  
% 2.23/1.03  fof(f38,plain,(
% 2.23/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8) | r1_tmap_1(X1,X0,X2,X5)) & sK8 = X5 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(sK8,u1_struct_0(X3)))) )),
% 2.23/1.03    introduced(choice_axiom,[])).
% 2.23/1.03  
% 2.23/1.03  fof(f37,plain,(
% 2.23/1.03    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,sK7)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,sK7)) & sK7 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(sK7,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK7,u1_struct_0(X1)))) )),
% 2.23/1.03    introduced(choice_axiom,[])).
% 2.23/1.03  
% 2.23/1.03  fof(f36,plain,(
% 2.23/1.03    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(sK6,u1_struct_0(X3)) & r2_hidden(X5,sK6) & v3_pre_topc(sK6,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 2.23/1.03    introduced(choice_axiom,[])).
% 2.23/1.03  
% 2.23/1.03  fof(f35,plain,(
% 2.23/1.03    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(sK5)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK5,X1) & ~v2_struct_0(sK5))) )),
% 2.23/1.03    introduced(choice_axiom,[])).
% 2.23/1.03  
% 2.23/1.03  fof(f34,plain,(
% 2.23/1.03    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X6) | ~r1_tmap_1(X1,X0,sK4,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X6) | r1_tmap_1(X1,X0,sK4,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 2.23/1.03    introduced(choice_axiom,[])).
% 2.23/1.03  
% 2.23/1.03  fof(f33,plain,(
% 2.23/1.03    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X6) | ~r1_tmap_1(sK3,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X6) | r1_tmap_1(sK3,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK3) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 2.23/1.03    introduced(choice_axiom,[])).
% 2.23/1.03  
% 2.23/1.03  fof(f32,plain,(
% 2.23/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6) | ~r1_tmap_1(X1,sK2,X2,X5)) & (r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6) | r1_tmap_1(X1,sK2,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.23/1.03    introduced(choice_axiom,[])).
% 2.23/1.03  
% 2.23/1.03  fof(f39,plain,(
% 2.23/1.03    (((((((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | ~r1_tmap_1(sK3,sK2,sK4,sK7)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | r1_tmap_1(sK3,sK2,sK4,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK5)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK3) & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.23/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f31,f38,f37,f36,f35,f34,f33,f32])).
% 2.23/1.03  
% 2.23/1.03  fof(f64,plain,(
% 2.23/1.03    m1_pre_topc(sK5,sK3)),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f6,axiom,(
% 2.23/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.23/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.03  
% 2.23/1.03  fof(f19,plain,(
% 2.23/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/1.03    inference(ennf_transformation,[],[f6])).
% 2.23/1.03  
% 2.23/1.03  fof(f20,plain,(
% 2.23/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/1.03    inference(flattening,[],[f19])).
% 2.23/1.03  
% 2.23/1.03  fof(f29,plain,(
% 2.23/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/1.03    inference(nnf_transformation,[],[f20])).
% 2.23/1.03  
% 2.23/1.03  fof(f53,plain,(
% 2.23/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/1.03    inference(cnf_transformation,[],[f29])).
% 2.23/1.03  
% 2.23/1.03  fof(f75,plain,(
% 2.23/1.03    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/1.03    inference(equality_resolution,[],[f53])).
% 2.23/1.03  
% 2.23/1.03  fof(f61,plain,(
% 2.23/1.03    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f60,plain,(
% 2.23/1.03    v1_funct_1(sK4)),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f1,axiom,(
% 2.23/1.03    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.23/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.03  
% 2.23/1.03  fof(f10,plain,(
% 2.23/1.03    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/1.03    inference(ennf_transformation,[],[f1])).
% 2.23/1.03  
% 2.23/1.03  fof(f11,plain,(
% 2.23/1.03    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/1.03    inference(flattening,[],[f10])).
% 2.23/1.03  
% 2.23/1.03  fof(f40,plain,(
% 2.23/1.03    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/1.03    inference(cnf_transformation,[],[f11])).
% 2.23/1.03  
% 2.23/1.03  fof(f57,plain,(
% 2.23/1.03    ~v2_struct_0(sK3)),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f58,plain,(
% 2.23/1.03    v2_pre_topc(sK3)),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f59,plain,(
% 2.23/1.03    l1_pre_topc(sK3)),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f63,plain,(
% 2.23/1.03    ~v2_struct_0(sK5)),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f56,plain,(
% 2.23/1.03    l1_pre_topc(sK2)),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f54,plain,(
% 2.23/1.03    ~v2_struct_0(sK2)),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f55,plain,(
% 2.23/1.03    v2_pre_topc(sK2)),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f62,plain,(
% 2.23/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f2,axiom,(
% 2.23/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.23/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.03  
% 2.23/1.03  fof(f9,plain,(
% 2.23/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.23/1.03    inference(pure_predicate_removal,[],[f2])).
% 2.23/1.03  
% 2.23/1.03  fof(f12,plain,(
% 2.23/1.03    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/1.03    inference(ennf_transformation,[],[f9])).
% 2.23/1.03  
% 2.23/1.03  fof(f13,plain,(
% 2.23/1.03    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/1.03    inference(flattening,[],[f12])).
% 2.23/1.03  
% 2.23/1.03  fof(f23,plain,(
% 2.23/1.03    ! [X2,X1,X0] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_connsp_2(sK0(X0,X1,X2),X0,X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.23/1.03    introduced(choice_axiom,[])).
% 2.23/1.03  
% 2.23/1.03  fof(f24,plain,(
% 2.23/1.03    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_connsp_2(sK0(X0,X1,X2),X0,X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f23])).
% 2.23/1.03  
% 2.23/1.03  fof(f44,plain,(
% 2.23/1.03    ( ! [X2,X0,X1] : (r1_tarski(sK0(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/1.03    inference(cnf_transformation,[],[f24])).
% 2.23/1.03  
% 2.23/1.03  fof(f42,plain,(
% 2.23/1.03    ( ! [X2,X0,X1] : (m1_connsp_2(sK0(X0,X1,X2),X0,X1) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/1.03    inference(cnf_transformation,[],[f24])).
% 2.23/1.03  
% 2.23/1.03  fof(f3,axiom,(
% 2.23/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 2.23/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.03  
% 2.23/1.03  fof(f14,plain,(
% 2.23/1.03    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/1.03    inference(ennf_transformation,[],[f3])).
% 2.23/1.03  
% 2.23/1.03  fof(f15,plain,(
% 2.23/1.03    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/1.03    inference(flattening,[],[f14])).
% 2.23/1.03  
% 2.23/1.03  fof(f25,plain,(
% 2.23/1.03    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/1.03    inference(nnf_transformation,[],[f15])).
% 2.23/1.03  
% 2.23/1.03  fof(f26,plain,(
% 2.23/1.03    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/1.03    inference(rectify,[],[f25])).
% 2.23/1.03  
% 2.23/1.03  fof(f27,plain,(
% 2.23/1.03    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.23/1.03    introduced(choice_axiom,[])).
% 2.23/1.03  
% 2.23/1.03  fof(f28,plain,(
% 2.23/1.03    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 2.23/1.03  
% 2.23/1.03  fof(f49,plain,(
% 2.23/1.03    ( ! [X2,X0,X3,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/1.03    inference(cnf_transformation,[],[f28])).
% 2.23/1.03  
% 2.23/1.03  fof(f5,axiom,(
% 2.23/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.23/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.03  
% 2.23/1.03  fof(f17,plain,(
% 2.23/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/1.03    inference(ennf_transformation,[],[f5])).
% 2.23/1.03  
% 2.23/1.03  fof(f18,plain,(
% 2.23/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/1.03    inference(flattening,[],[f17])).
% 2.23/1.03  
% 2.23/1.03  fof(f51,plain,(
% 2.23/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/1.03    inference(cnf_transformation,[],[f18])).
% 2.23/1.03  
% 2.23/1.03  fof(f74,plain,(
% 2.23/1.03    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/1.03    inference(equality_resolution,[],[f51])).
% 2.23/1.03  
% 2.23/1.03  fof(f71,plain,(
% 2.23/1.03    sK7 = sK8),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f4,axiom,(
% 2.23/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.23/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.03  
% 2.23/1.03  fof(f16,plain,(
% 2.23/1.03    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.23/1.03    inference(ennf_transformation,[],[f4])).
% 2.23/1.03  
% 2.23/1.03  fof(f50,plain,(
% 2.23/1.03    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.23/1.03    inference(cnf_transformation,[],[f16])).
% 2.23/1.03  
% 2.23/1.03  fof(f73,plain,(
% 2.23/1.03    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | ~r1_tmap_1(sK3,sK2,sK4,sK7)),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f72,plain,(
% 2.23/1.03    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | r1_tmap_1(sK3,sK2,sK4,sK7)),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f70,plain,(
% 2.23/1.03    r1_tarski(sK6,u1_struct_0(sK5))),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f69,plain,(
% 2.23/1.03    r2_hidden(sK7,sK6)),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f68,plain,(
% 2.23/1.03    v3_pre_topc(sK6,sK3)),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f67,plain,(
% 2.23/1.03    m1_subset_1(sK8,u1_struct_0(sK5))),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f66,plain,(
% 2.23/1.03    m1_subset_1(sK7,u1_struct_0(sK3))),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  fof(f65,plain,(
% 2.23/1.03    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.23/1.03    inference(cnf_transformation,[],[f39])).
% 2.23/1.03  
% 2.23/1.03  cnf(c_23,negated_conjecture,
% 2.23/1.03      ( m1_pre_topc(sK5,sK3) ),
% 2.23/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_12,plain,
% 2.23/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 2.23/1.03      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.23/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.23/1.03      | ~ m1_connsp_2(X5,X0,X3)
% 2.23/1.03      | ~ m1_pre_topc(X4,X0)
% 2.23/1.03      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.23/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.23/1.03      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.23/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.23/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/1.03      | ~ v1_funct_1(X2)
% 2.23/1.03      | v2_struct_0(X1)
% 2.23/1.03      | v2_struct_0(X0)
% 2.23/1.03      | v2_struct_0(X4)
% 2.23/1.03      | ~ v2_pre_topc(X1)
% 2.23/1.03      | ~ v2_pre_topc(X0)
% 2.23/1.03      | ~ l1_pre_topc(X1)
% 2.23/1.03      | ~ l1_pre_topc(X0) ),
% 2.23/1.03      inference(cnf_transformation,[],[f75]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_26,negated_conjecture,
% 2.23/1.03      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 2.23/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_550,plain,
% 2.23/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 2.23/1.03      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.23/1.03      | ~ m1_connsp_2(X5,X0,X3)
% 2.23/1.03      | ~ m1_pre_topc(X4,X0)
% 2.23/1.03      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.23/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.23/1.03      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.23/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.23/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/1.03      | ~ v1_funct_1(X2)
% 2.23/1.03      | v2_struct_0(X1)
% 2.23/1.03      | v2_struct_0(X0)
% 2.23/1.03      | v2_struct_0(X4)
% 2.23/1.03      | ~ v2_pre_topc(X1)
% 2.23/1.03      | ~ v2_pre_topc(X0)
% 2.23/1.03      | ~ l1_pre_topc(X1)
% 2.23/1.03      | ~ l1_pre_topc(X0)
% 2.23/1.03      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.23/1.03      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.23/1.03      | sK4 != X2 ),
% 2.23/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_26]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_551,plain,
% 2.23/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.23/1.03      | r1_tmap_1(X2,X1,sK4,X3)
% 2.23/1.03      | ~ m1_connsp_2(X4,X2,X3)
% 2.23/1.03      | ~ m1_pre_topc(X0,X2)
% 2.23/1.03      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.23/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.23/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.23/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.23/1.03      | ~ v1_funct_1(sK4)
% 2.23/1.03      | v2_struct_0(X1)
% 2.23/1.03      | v2_struct_0(X2)
% 2.23/1.03      | v2_struct_0(X0)
% 2.23/1.03      | ~ v2_pre_topc(X1)
% 2.23/1.03      | ~ v2_pre_topc(X2)
% 2.23/1.03      | ~ l1_pre_topc(X1)
% 2.23/1.03      | ~ l1_pre_topc(X2)
% 2.23/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.23/1.03      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.23/1.03      inference(unflattening,[status(thm)],[c_550]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_27,negated_conjecture,
% 2.23/1.03      ( v1_funct_1(sK4) ),
% 2.23/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_555,plain,
% 2.23/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.23/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.23/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.23/1.03      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.23/1.03      | ~ m1_pre_topc(X0,X2)
% 2.23/1.03      | ~ m1_connsp_2(X4,X2,X3)
% 2.23/1.03      | r1_tmap_1(X2,X1,sK4,X3)
% 2.23/1.03      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.23/1.03      | v2_struct_0(X1)
% 2.23/1.03      | v2_struct_0(X2)
% 2.23/1.03      | v2_struct_0(X0)
% 2.23/1.03      | ~ v2_pre_topc(X1)
% 2.23/1.03      | ~ v2_pre_topc(X2)
% 2.23/1.03      | ~ l1_pre_topc(X1)
% 2.23/1.03      | ~ l1_pre_topc(X2)
% 2.23/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.23/1.03      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.23/1.03      inference(global_propositional_subsumption,
% 2.23/1.03                [status(thm)],
% 2.23/1.03                [c_551,c_27]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_556,plain,
% 2.23/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.23/1.03      | r1_tmap_1(X2,X1,sK4,X3)
% 2.23/1.03      | ~ m1_connsp_2(X4,X2,X3)
% 2.23/1.03      | ~ m1_pre_topc(X0,X2)
% 2.23/1.03      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.23/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.23/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.23/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.23/1.03      | v2_struct_0(X1)
% 2.23/1.03      | v2_struct_0(X2)
% 2.23/1.03      | v2_struct_0(X0)
% 2.23/1.03      | ~ v2_pre_topc(X1)
% 2.23/1.03      | ~ v2_pre_topc(X2)
% 2.23/1.03      | ~ l1_pre_topc(X1)
% 2.23/1.03      | ~ l1_pre_topc(X2)
% 2.23/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.23/1.03      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.23/1.03      inference(renaming,[status(thm)],[c_555]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_0,plain,
% 2.23/1.03      ( ~ m1_connsp_2(X0,X1,X2)
% 2.23/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.23/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.23/1.03      | v2_struct_0(X1)
% 2.23/1.03      | ~ v2_pre_topc(X1)
% 2.23/1.03      | ~ l1_pre_topc(X1) ),
% 2.23/1.03      inference(cnf_transformation,[],[f40]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_597,plain,
% 2.23/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.23/1.03      | r1_tmap_1(X2,X1,sK4,X3)
% 2.23/1.03      | ~ m1_connsp_2(X4,X2,X3)
% 2.23/1.03      | ~ m1_pre_topc(X0,X2)
% 2.23/1.03      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.23/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.23/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.23/1.03      | v2_struct_0(X1)
% 2.23/1.03      | v2_struct_0(X2)
% 2.23/1.03      | v2_struct_0(X0)
% 2.23/1.03      | ~ v2_pre_topc(X1)
% 2.23/1.03      | ~ v2_pre_topc(X2)
% 2.23/1.03      | ~ l1_pre_topc(X1)
% 2.23/1.03      | ~ l1_pre_topc(X2)
% 2.23/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.23/1.03      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.23/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_556,c_0]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_730,plain,
% 2.23/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.23/1.03      | r1_tmap_1(X2,X1,sK4,X3)
% 2.23/1.03      | ~ m1_connsp_2(X4,X2,X3)
% 2.23/1.03      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.23/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.23/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.23/1.03      | v2_struct_0(X2)
% 2.23/1.03      | v2_struct_0(X1)
% 2.23/1.03      | v2_struct_0(X0)
% 2.23/1.03      | ~ v2_pre_topc(X2)
% 2.23/1.03      | ~ v2_pre_topc(X1)
% 2.23/1.03      | ~ l1_pre_topc(X2)
% 2.23/1.03      | ~ l1_pre_topc(X1)
% 2.23/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.23/1.03      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.23/1.03      | sK3 != X2
% 2.23/1.03      | sK5 != X0 ),
% 2.23/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_597]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_731,plain,
% 2.23/1.03      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.23/1.03      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.23/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 2.23/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.23/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.23/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.23/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.23/1.03      | v2_struct_0(X0)
% 2.23/1.03      | v2_struct_0(sK3)
% 2.23/1.03      | v2_struct_0(sK5)
% 2.23/1.03      | ~ v2_pre_topc(X0)
% 2.23/1.03      | ~ v2_pre_topc(sK3)
% 2.23/1.03      | ~ l1_pre_topc(X0)
% 2.23/1.03      | ~ l1_pre_topc(sK3)
% 2.23/1.03      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.23/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.23/1.03      inference(unflattening,[status(thm)],[c_730]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_30,negated_conjecture,
% 2.23/1.03      ( ~ v2_struct_0(sK3) ),
% 2.23/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_29,negated_conjecture,
% 2.23/1.03      ( v2_pre_topc(sK3) ),
% 2.23/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_28,negated_conjecture,
% 2.23/1.03      ( l1_pre_topc(sK3) ),
% 2.23/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_24,negated_conjecture,
% 2.23/1.03      ( ~ v2_struct_0(sK5) ),
% 2.23/1.03      inference(cnf_transformation,[],[f63]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_735,plain,
% 2.23/1.03      ( ~ l1_pre_topc(X0)
% 2.23/1.03      | r1_tmap_1(sK3,X0,sK4,X1)
% 2.23/1.03      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.23/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 2.23/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.23/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.23/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.23/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.23/1.03      | v2_struct_0(X0)
% 2.23/1.03      | ~ v2_pre_topc(X0)
% 2.23/1.03      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.23/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.23/1.03      inference(global_propositional_subsumption,
% 2.23/1.03                [status(thm)],
% 2.23/1.03                [c_731,c_30,c_29,c_28,c_24]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_736,plain,
% 2.23/1.03      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.23/1.03      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.23/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 2.23/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.23/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.23/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.23/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.23/1.03      | v2_struct_0(X0)
% 2.23/1.03      | ~ v2_pre_topc(X0)
% 2.23/1.03      | ~ l1_pre_topc(X0)
% 2.23/1.03      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.23/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.23/1.03      inference(renaming,[status(thm)],[c_735]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_31,negated_conjecture,
% 2.23/1.03      ( l1_pre_topc(sK2) ),
% 2.23/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_1712,plain,
% 2.23/1.03      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.23/1.03      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.23/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 2.23/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.23/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.23/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.23/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.23/1.03      | v2_struct_0(X0)
% 2.23/1.03      | ~ v2_pre_topc(X0)
% 2.23/1.03      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.23/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.23/1.03      | sK2 != X0 ),
% 2.23/1.03      inference(resolution_lifted,[status(thm)],[c_736,c_31]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_1713,plain,
% 2.23/1.03      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.23/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.23/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 2.23/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.23/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.23/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.23/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 2.23/1.03      | v2_struct_0(sK2)
% 2.23/1.03      | ~ v2_pre_topc(sK2)
% 2.23/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.23/1.03      inference(unflattening,[status(thm)],[c_1712]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_33,negated_conjecture,
% 2.23/1.03      ( ~ v2_struct_0(sK2) ),
% 2.23/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_32,negated_conjecture,
% 2.23/1.03      ( v2_pre_topc(sK2) ),
% 2.23/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_25,negated_conjecture,
% 2.23/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 2.23/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_1717,plain,
% 2.23/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.23/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.23/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.23/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 2.23/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.23/1.03      | r1_tmap_1(sK3,sK2,sK4,X0)
% 2.23/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.23/1.03      inference(global_propositional_subsumption,
% 2.23/1.03                [status(thm)],
% 2.23/1.03                [c_1713,c_33,c_32,c_25]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_1718,plain,
% 2.23/1.03      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.23/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.23/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 2.23/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.23/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.23/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.23/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.23/1.03      inference(renaming,[status(thm)],[c_1717]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_3133,plain,
% 2.23/1.03      ( r1_tmap_1(sK3,sK2,sK4,X0_54)
% 2.23/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
% 2.23/1.03      | ~ m1_connsp_2(X1_54,sK3,X0_54)
% 2.23/1.03      | ~ r1_tarski(X1_54,u1_struct_0(sK5))
% 2.23/1.03      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.23/1.03      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 2.23/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.23/1.03      inference(subtyping,[status(esa)],[c_1718]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_3360,plain,
% 2.23/1.03      ( r1_tmap_1(sK3,sK2,sK4,X0_54)
% 2.23/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
% 2.23/1.03      | ~ m1_connsp_2(X1_54,sK3,X0_54)
% 2.23/1.03      | ~ r1_tarski(X1_54,u1_struct_0(sK5))
% 2.23/1.03      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.23/1.03      | ~ m1_subset_1(X0_54,u1_struct_0(sK5)) ),
% 2.23/1.03      inference(equality_resolution_simp,[status(thm)],[c_3133]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_4975,plain,
% 2.23/1.03      ( r1_tmap_1(sK3,sK2,sK4,X0_54)
% 2.23/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
% 2.23/1.03      | ~ m1_connsp_2(sK0(sK3,sK7,u1_struct_0(sK5)),sK3,X0_54)
% 2.23/1.03      | ~ r1_tarski(sK0(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5))
% 2.23/1.03      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.23/1.03      | ~ m1_subset_1(X0_54,u1_struct_0(sK5)) ),
% 2.23/1.03      inference(instantiation,[status(thm)],[c_3360]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_5699,plain,
% 2.23/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.23/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.23/1.03      | ~ m1_connsp_2(sK0(sK3,sK7,u1_struct_0(sK5)),sK3,sK7)
% 2.23/1.03      | ~ r1_tarski(sK0(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5))
% 2.23/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.23/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 2.23/1.03      inference(instantiation,[status(thm)],[c_4975]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_3181,plain,
% 2.23/1.03      ( ~ r1_tmap_1(X0_53,X1_53,X0_54,X1_54)
% 2.23/1.03      | r1_tmap_1(X0_53,X1_53,X2_54,X3_54)
% 2.23/1.03      | X2_54 != X0_54
% 2.23/1.03      | X3_54 != X1_54 ),
% 2.23/1.03      theory(equality) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_4477,plain,
% 2.23/1.03      ( r1_tmap_1(sK5,sK2,X0_54,X1_54)
% 2.23/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.23/1.03      | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.23/1.03      | X1_54 != sK7 ),
% 2.23/1.03      inference(instantiation,[status(thm)],[c_3181]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_5078,plain,
% 2.23/1.03      ( r1_tmap_1(sK5,sK2,X0_54,sK8)
% 2.23/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.23/1.03      | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.23/1.03      | sK8 != sK7 ),
% 2.23/1.03      inference(instantiation,[status(thm)],[c_4477]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_5563,plain,
% 2.23/1.03      ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.23/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 2.23/1.03      | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.23/1.03      | sK8 != sK7 ),
% 2.23/1.03      inference(instantiation,[status(thm)],[c_5078]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_3173,plain,
% 2.23/1.03      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 2.23/1.03      theory(equality) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_4525,plain,
% 2.23/1.03      ( X0_54 != X1_54 | X0_54 = sK7 | sK7 != X1_54 ),
% 2.23/1.03      inference(instantiation,[status(thm)],[c_3173]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_4721,plain,
% 2.23/1.03      ( X0_54 = sK7 | X0_54 != sK8 | sK7 != sK8 ),
% 2.23/1.03      inference(instantiation,[status(thm)],[c_4525]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_4824,plain,
% 2.23/1.03      ( sK7 != sK8 | sK8 = sK7 | sK8 != sK8 ),
% 2.23/1.03      inference(instantiation,[status(thm)],[c_4721]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_1,plain,
% 2.23/1.03      ( ~ m1_connsp_2(X0,X1,X2)
% 2.23/1.03      | r1_tarski(sK0(X1,X2,X0),X0)
% 2.23/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.23/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.23/1.03      | v2_struct_0(X1)
% 2.23/1.03      | ~ v2_pre_topc(X1)
% 2.23/1.03      | ~ l1_pre_topc(X1) ),
% 2.23/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_239,plain,
% 2.23/1.03      ( r1_tarski(sK0(X1,X2,X0),X0)
% 2.23/1.03      | ~ m1_connsp_2(X0,X1,X2)
% 2.23/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.23/1.03      | v2_struct_0(X1)
% 2.23/1.03      | ~ v2_pre_topc(X1)
% 2.23/1.03      | ~ l1_pre_topc(X1) ),
% 2.23/1.03      inference(global_propositional_subsumption,[status(thm)],[c_1,c_0]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_240,plain,
% 2.23/1.03      ( ~ m1_connsp_2(X0,X1,X2)
% 2.23/1.03      | r1_tarski(sK0(X1,X2,X0),X0)
% 2.23/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.23/1.03      | v2_struct_0(X1)
% 2.23/1.03      | ~ v2_pre_topc(X1)
% 2.23/1.03      | ~ l1_pre_topc(X1) ),
% 2.23/1.03      inference(renaming,[status(thm)],[c_239]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_1202,plain,
% 2.23/1.03      ( ~ m1_connsp_2(X0,X1,X2)
% 2.23/1.03      | r1_tarski(sK0(X1,X2,X0),X0)
% 2.23/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.23/1.03      | v2_struct_0(X1)
% 2.23/1.03      | ~ v2_pre_topc(X1)
% 2.23/1.03      | sK3 != X1 ),
% 2.23/1.03      inference(resolution_lifted,[status(thm)],[c_240,c_28]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_1203,plain,
% 2.23/1.03      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.23/1.03      | r1_tarski(sK0(sK3,X1,X0),X0)
% 2.23/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.23/1.03      | v2_struct_0(sK3)
% 2.23/1.03      | ~ v2_pre_topc(sK3) ),
% 2.23/1.03      inference(unflattening,[status(thm)],[c_1202]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_1207,plain,
% 2.23/1.03      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.23/1.03      | r1_tarski(sK0(sK3,X1,X0),X0)
% 2.23/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 2.23/1.03      inference(global_propositional_subsumption,
% 2.23/1.03                [status(thm)],
% 2.23/1.03                [c_1203,c_30,c_29]) ).
% 2.23/1.03  
% 2.23/1.03  cnf(c_3155,plain,
% 2.23/1.03      ( ~ m1_connsp_2(X0_54,sK3,X1_54)
% 2.23/1.03      | r1_tarski(sK0(sK3,X1_54,X0_54),X0_54)
% 2.23/1.03      | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
% 2.23/1.04      inference(subtyping,[status(esa)],[c_1207]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_4408,plain,
% 2.23/1.04      ( ~ m1_connsp_2(X0_54,sK3,sK7)
% 2.23/1.04      | r1_tarski(sK0(sK3,sK7,X0_54),X0_54)
% 2.23/1.04      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.23/1.04      inference(instantiation,[status(thm)],[c_3155]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_4790,plain,
% 2.23/1.04      ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
% 2.23/1.04      | r1_tarski(sK0(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5))
% 2.23/1.04      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.23/1.04      inference(instantiation,[status(thm)],[c_4408]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_3,plain,
% 2.23/1.04      ( ~ m1_connsp_2(X0,X1,X2)
% 2.23/1.04      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 2.23/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.23/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.23/1.04      | v2_struct_0(X1)
% 2.23/1.04      | ~ v2_pre_topc(X1)
% 2.23/1.04      | ~ l1_pre_topc(X1) ),
% 2.23/1.04      inference(cnf_transformation,[],[f42]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_225,plain,
% 2.23/1.04      ( m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 2.23/1.04      | ~ m1_connsp_2(X0,X1,X2)
% 2.23/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.23/1.04      | v2_struct_0(X1)
% 2.23/1.04      | ~ v2_pre_topc(X1)
% 2.23/1.04      | ~ l1_pre_topc(X1) ),
% 2.23/1.04      inference(global_propositional_subsumption,[status(thm)],[c_3,c_0]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_226,plain,
% 2.23/1.04      ( ~ m1_connsp_2(X0,X1,X2)
% 2.23/1.04      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 2.23/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.23/1.04      | v2_struct_0(X1)
% 2.23/1.04      | ~ v2_pre_topc(X1)
% 2.23/1.04      | ~ l1_pre_topc(X1) ),
% 2.23/1.04      inference(renaming,[status(thm)],[c_225]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_1244,plain,
% 2.23/1.04      ( ~ m1_connsp_2(X0,X1,X2)
% 2.23/1.04      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 2.23/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.23/1.04      | v2_struct_0(X1)
% 2.23/1.04      | ~ v2_pre_topc(X1)
% 2.23/1.04      | sK3 != X1 ),
% 2.23/1.04      inference(resolution_lifted,[status(thm)],[c_226,c_28]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_1245,plain,
% 2.23/1.04      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.23/1.04      | m1_connsp_2(sK0(sK3,X1,X0),sK3,X1)
% 2.23/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.23/1.04      | v2_struct_0(sK3)
% 2.23/1.04      | ~ v2_pre_topc(sK3) ),
% 2.23/1.04      inference(unflattening,[status(thm)],[c_1244]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_1249,plain,
% 2.23/1.04      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.23/1.04      | m1_connsp_2(sK0(sK3,X1,X0),sK3,X1)
% 2.23/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 2.23/1.04      inference(global_propositional_subsumption,
% 2.23/1.04                [status(thm)],
% 2.23/1.04                [c_1245,c_30,c_29]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_3153,plain,
% 2.23/1.04      ( ~ m1_connsp_2(X0_54,sK3,X1_54)
% 2.23/1.04      | m1_connsp_2(sK0(sK3,X1_54,X0_54),sK3,X1_54)
% 2.23/1.04      | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
% 2.23/1.04      inference(subtyping,[status(esa)],[c_1249]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_4403,plain,
% 2.23/1.04      ( ~ m1_connsp_2(X0_54,sK3,sK7)
% 2.23/1.04      | m1_connsp_2(sK0(sK3,sK7,X0_54),sK3,sK7)
% 2.23/1.04      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.23/1.04      inference(instantiation,[status(thm)],[c_3153]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_4792,plain,
% 2.23/1.04      ( m1_connsp_2(sK0(sK3,sK7,u1_struct_0(sK5)),sK3,sK7)
% 2.23/1.04      | ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
% 2.23/1.04      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.23/1.04      inference(instantiation,[status(thm)],[c_4403]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_3175,plain,
% 2.23/1.04      ( ~ m1_subset_1(X0_54,X1_54)
% 2.23/1.04      | m1_subset_1(X2_54,X3_54)
% 2.23/1.04      | X2_54 != X0_54
% 2.23/1.04      | X3_54 != X1_54 ),
% 2.23/1.04      theory(equality) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_4437,plain,
% 2.23/1.04      ( m1_subset_1(X0_54,X1_54)
% 2.23/1.04      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.23/1.04      | X1_54 != u1_struct_0(sK5)
% 2.23/1.04      | X0_54 != sK8 ),
% 2.23/1.04      inference(instantiation,[status(thm)],[c_3175]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_4506,plain,
% 2.23/1.04      ( m1_subset_1(sK7,X0_54)
% 2.23/1.04      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.23/1.04      | X0_54 != u1_struct_0(sK5)
% 2.23/1.04      | sK7 != sK8 ),
% 2.23/1.04      inference(instantiation,[status(thm)],[c_4437]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_4757,plain,
% 2.23/1.04      ( m1_subset_1(sK7,u1_struct_0(sK5))
% 2.23/1.04      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.23/1.04      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 2.23/1.04      | sK7 != sK8 ),
% 2.23/1.04      inference(instantiation,[status(thm)],[c_4506]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_5,plain,
% 2.23/1.04      ( m1_connsp_2(X0,X1,X2)
% 2.23/1.04      | ~ r2_hidden(X2,X3)
% 2.23/1.04      | ~ v3_pre_topc(X3,X1)
% 2.23/1.04      | ~ r1_tarski(X3,X0)
% 2.23/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.23/1.04      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.23/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.23/1.04      | v2_struct_0(X1)
% 2.23/1.04      | ~ v2_pre_topc(X1)
% 2.23/1.04      | ~ l1_pre_topc(X1) ),
% 2.23/1.04      inference(cnf_transformation,[],[f49]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_1370,plain,
% 2.23/1.04      ( m1_connsp_2(X0,X1,X2)
% 2.23/1.04      | ~ r2_hidden(X2,X3)
% 2.23/1.04      | ~ v3_pre_topc(X3,X1)
% 2.23/1.04      | ~ r1_tarski(X3,X0)
% 2.23/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.23/1.04      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.23/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.23/1.04      | v2_struct_0(X1)
% 2.23/1.04      | ~ v2_pre_topc(X1)
% 2.23/1.04      | sK3 != X1 ),
% 2.23/1.04      inference(resolution_lifted,[status(thm)],[c_5,c_28]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_1371,plain,
% 2.23/1.04      ( m1_connsp_2(X0,sK3,X1)
% 2.23/1.04      | ~ r2_hidden(X1,X2)
% 2.23/1.04      | ~ v3_pre_topc(X2,sK3)
% 2.23/1.04      | ~ r1_tarski(X2,X0)
% 2.23/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.23/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.23/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.23/1.04      | v2_struct_0(sK3)
% 2.23/1.04      | ~ v2_pre_topc(sK3) ),
% 2.23/1.04      inference(unflattening,[status(thm)],[c_1370]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_1375,plain,
% 2.23/1.04      ( m1_connsp_2(X0,sK3,X1)
% 2.23/1.04      | ~ r2_hidden(X1,X2)
% 2.23/1.04      | ~ v3_pre_topc(X2,sK3)
% 2.23/1.04      | ~ r1_tarski(X2,X0)
% 2.23/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.23/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.23/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 2.23/1.04      inference(global_propositional_subsumption,
% 2.23/1.04                [status(thm)],
% 2.23/1.04                [c_1371,c_30,c_29]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_3147,plain,
% 2.23/1.04      ( m1_connsp_2(X0_54,sK3,X1_54)
% 2.23/1.04      | ~ r2_hidden(X1_54,X2_54)
% 2.23/1.04      | ~ v3_pre_topc(X2_54,sK3)
% 2.23/1.04      | ~ r1_tarski(X2_54,X0_54)
% 2.23/1.04      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.23/1.04      | ~ m1_subset_1(X2_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.23/1.04      | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
% 2.23/1.04      inference(subtyping,[status(esa)],[c_1375]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_4413,plain,
% 2.23/1.04      ( m1_connsp_2(X0_54,sK3,X1_54)
% 2.23/1.04      | ~ r2_hidden(X1_54,sK6)
% 2.23/1.04      | ~ v3_pre_topc(sK6,sK3)
% 2.23/1.04      | ~ r1_tarski(sK6,X0_54)
% 2.23/1.04      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.23/1.04      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 2.23/1.04      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.23/1.04      inference(instantiation,[status(thm)],[c_3147]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_4554,plain,
% 2.23/1.04      ( m1_connsp_2(X0_54,sK3,sK7)
% 2.23/1.04      | ~ r2_hidden(sK7,sK6)
% 2.23/1.04      | ~ v3_pre_topc(sK6,sK3)
% 2.23/1.04      | ~ r1_tarski(sK6,X0_54)
% 2.23/1.04      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.23/1.04      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.23/1.04      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.23/1.04      inference(instantiation,[status(thm)],[c_4413]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_4654,plain,
% 2.23/1.04      ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
% 2.23/1.04      | ~ r2_hidden(sK7,sK6)
% 2.23/1.04      | ~ v3_pre_topc(sK6,sK3)
% 2.23/1.04      | ~ r1_tarski(sK6,u1_struct_0(sK5))
% 2.23/1.04      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.23/1.04      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.23/1.04      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.23/1.04      inference(instantiation,[status(thm)],[c_4554]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_3172,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_4645,plain,
% 2.23/1.04      ( k2_tmap_1(sK3,sK2,sK4,sK5) = k2_tmap_1(sK3,sK2,sK4,sK5) ),
% 2.23/1.04      inference(instantiation,[status(thm)],[c_3172]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_4472,plain,
% 2.23/1.04      ( r1_tmap_1(sK5,sK2,X0_54,X1_54)
% 2.23/1.04      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 2.23/1.04      | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.23/1.04      | X1_54 != sK8 ),
% 2.23/1.04      inference(instantiation,[status(thm)],[c_3181]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_4546,plain,
% 2.23/1.04      ( r1_tmap_1(sK5,sK2,X0_54,sK7)
% 2.23/1.04      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 2.23/1.04      | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.23/1.04      | sK7 != sK8 ),
% 2.23/1.04      inference(instantiation,[status(thm)],[c_4472]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_4644,plain,
% 2.23/1.04      ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.23/1.04      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 2.23/1.04      | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.23/1.04      | sK7 != sK8 ),
% 2.23/1.04      inference(instantiation,[status(thm)],[c_4546]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_4571,plain,
% 2.23/1.04      ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
% 2.23/1.04      inference(instantiation,[status(thm)],[c_3172]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_4512,plain,
% 2.23/1.04      ( sK8 = sK8 ),
% 2.23/1.04      inference(instantiation,[status(thm)],[c_3172]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_11,plain,
% 2.23/1.04      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.23/1.04      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.23/1.04      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.23/1.04      | ~ m1_pre_topc(X4,X0)
% 2.23/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.23/1.04      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.23/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/1.04      | ~ v1_funct_1(X2)
% 2.23/1.04      | v2_struct_0(X1)
% 2.23/1.04      | v2_struct_0(X0)
% 2.23/1.04      | v2_struct_0(X4)
% 2.23/1.04      | ~ v2_pre_topc(X1)
% 2.23/1.04      | ~ v2_pre_topc(X0)
% 2.23/1.04      | ~ l1_pre_topc(X1)
% 2.23/1.04      | ~ l1_pre_topc(X0) ),
% 2.23/1.04      inference(cnf_transformation,[],[f74]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_618,plain,
% 2.23/1.04      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.23/1.04      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.23/1.04      | ~ m1_pre_topc(X4,X0)
% 2.23/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.23/1.04      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.23/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/1.04      | ~ v1_funct_1(X2)
% 2.23/1.04      | v2_struct_0(X1)
% 2.23/1.04      | v2_struct_0(X0)
% 2.23/1.04      | v2_struct_0(X4)
% 2.23/1.04      | ~ v2_pre_topc(X1)
% 2.23/1.04      | ~ v2_pre_topc(X0)
% 2.23/1.04      | ~ l1_pre_topc(X1)
% 2.23/1.04      | ~ l1_pre_topc(X0)
% 2.23/1.04      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.23/1.04      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.23/1.04      | sK4 != X2 ),
% 2.23/1.04      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_619,plain,
% 2.23/1.04      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.23/1.04      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.23/1.04      | ~ m1_pre_topc(X0,X2)
% 2.23/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/1.04      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.23/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.23/1.04      | ~ v1_funct_1(sK4)
% 2.23/1.04      | v2_struct_0(X1)
% 2.23/1.04      | v2_struct_0(X2)
% 2.23/1.04      | v2_struct_0(X0)
% 2.23/1.04      | ~ v2_pre_topc(X1)
% 2.23/1.04      | ~ v2_pre_topc(X2)
% 2.23/1.04      | ~ l1_pre_topc(X1)
% 2.23/1.04      | ~ l1_pre_topc(X2)
% 2.23/1.04      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.23/1.04      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.23/1.04      inference(unflattening,[status(thm)],[c_618]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_623,plain,
% 2.23/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.23/1.04      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.23/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/1.04      | ~ m1_pre_topc(X0,X2)
% 2.23/1.04      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.23/1.04      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.23/1.04      | v2_struct_0(X1)
% 2.23/1.04      | v2_struct_0(X2)
% 2.23/1.04      | v2_struct_0(X0)
% 2.23/1.04      | ~ v2_pre_topc(X1)
% 2.23/1.04      | ~ v2_pre_topc(X2)
% 2.23/1.04      | ~ l1_pre_topc(X1)
% 2.23/1.04      | ~ l1_pre_topc(X2)
% 2.23/1.04      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.23/1.04      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.23/1.04      inference(global_propositional_subsumption,
% 2.23/1.04                [status(thm)],
% 2.23/1.04                [c_619,c_27]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_624,plain,
% 2.23/1.04      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.23/1.04      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.23/1.04      | ~ m1_pre_topc(X0,X2)
% 2.23/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/1.04      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.23/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.23/1.04      | v2_struct_0(X1)
% 2.23/1.04      | v2_struct_0(X2)
% 2.23/1.04      | v2_struct_0(X0)
% 2.23/1.04      | ~ v2_pre_topc(X1)
% 2.23/1.04      | ~ v2_pre_topc(X2)
% 2.23/1.04      | ~ l1_pre_topc(X1)
% 2.23/1.04      | ~ l1_pre_topc(X2)
% 2.23/1.04      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.23/1.04      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.23/1.04      inference(renaming,[status(thm)],[c_623]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_688,plain,
% 2.23/1.04      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.23/1.04      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.23/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/1.04      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.23/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.23/1.04      | v2_struct_0(X2)
% 2.23/1.04      | v2_struct_0(X1)
% 2.23/1.04      | v2_struct_0(X0)
% 2.23/1.04      | ~ v2_pre_topc(X2)
% 2.23/1.04      | ~ v2_pre_topc(X1)
% 2.23/1.04      | ~ l1_pre_topc(X2)
% 2.23/1.04      | ~ l1_pre_topc(X1)
% 2.23/1.04      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.23/1.04      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.23/1.04      | sK3 != X2
% 2.23/1.04      | sK5 != X0 ),
% 2.23/1.04      inference(resolution_lifted,[status(thm)],[c_23,c_624]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_689,plain,
% 2.23/1.04      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.23/1.04      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.23/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.23/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.23/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.23/1.04      | v2_struct_0(X0)
% 2.23/1.04      | v2_struct_0(sK3)
% 2.23/1.04      | v2_struct_0(sK5)
% 2.23/1.04      | ~ v2_pre_topc(X0)
% 2.23/1.04      | ~ v2_pre_topc(sK3)
% 2.23/1.04      | ~ l1_pre_topc(X0)
% 2.23/1.04      | ~ l1_pre_topc(sK3)
% 2.23/1.04      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.23/1.04      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.23/1.04      inference(unflattening,[status(thm)],[c_688]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_693,plain,
% 2.23/1.04      ( ~ l1_pre_topc(X0)
% 2.23/1.04      | ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.23/1.04      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.23/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.23/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.23/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.23/1.04      | v2_struct_0(X0)
% 2.23/1.04      | ~ v2_pre_topc(X0)
% 2.23/1.04      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.23/1.04      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.23/1.04      inference(global_propositional_subsumption,
% 2.23/1.04                [status(thm)],
% 2.23/1.04                [c_689,c_30,c_29,c_28,c_24]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_694,plain,
% 2.23/1.04      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.23/1.04      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.23/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.23/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.23/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.23/1.04      | v2_struct_0(X0)
% 2.23/1.04      | ~ v2_pre_topc(X0)
% 2.23/1.04      | ~ l1_pre_topc(X0)
% 2.23/1.04      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.23/1.04      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.23/1.04      inference(renaming,[status(thm)],[c_693]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_1745,plain,
% 2.23/1.04      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.23/1.04      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.23/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.23/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.23/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.23/1.04      | v2_struct_0(X0)
% 2.23/1.04      | ~ v2_pre_topc(X0)
% 2.23/1.04      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.23/1.04      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.23/1.04      | sK2 != X0 ),
% 2.23/1.04      inference(resolution_lifted,[status(thm)],[c_694,c_31]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_1746,plain,
% 2.23/1.04      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.23/1.04      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.23/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.23/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.23/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 2.23/1.04      | v2_struct_0(sK2)
% 2.23/1.04      | ~ v2_pre_topc(sK2)
% 2.23/1.04      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.23/1.04      inference(unflattening,[status(thm)],[c_1745]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_1750,plain,
% 2.23/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.23/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.23/1.04      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.23/1.04      | ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.23/1.04      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.23/1.04      inference(global_propositional_subsumption,
% 2.23/1.04                [status(thm)],
% 2.23/1.04                [c_1746,c_33,c_32,c_25]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_1751,plain,
% 2.23/1.04      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.23/1.04      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.23/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.23/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.23/1.04      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.23/1.04      inference(renaming,[status(thm)],[c_1750]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_3132,plain,
% 2.23/1.04      ( ~ r1_tmap_1(sK3,sK2,sK4,X0_54)
% 2.23/1.04      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
% 2.23/1.04      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.23/1.04      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 2.23/1.04      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.23/1.04      inference(subtyping,[status(esa)],[c_1751]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_3364,plain,
% 2.23/1.04      ( ~ r1_tmap_1(sK3,sK2,sK4,X0_54)
% 2.23/1.04      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
% 2.23/1.04      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.23/1.04      | ~ m1_subset_1(X0_54,u1_struct_0(sK5)) ),
% 2.23/1.04      inference(equality_resolution_simp,[status(thm)],[c_3132]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_4418,plain,
% 2.23/1.04      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.23/1.04      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.23/1.04      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.23/1.04      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 2.23/1.04      inference(instantiation,[status(thm)],[c_3364]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_16,negated_conjecture,
% 2.23/1.04      ( sK7 = sK8 ),
% 2.23/1.04      inference(cnf_transformation,[],[f71]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_3164,negated_conjecture,
% 2.23/1.04      ( sK7 = sK8 ),
% 2.23/1.04      inference(subtyping,[status(esa)],[c_16]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_10,plain,
% 2.23/1.04      ( ~ m1_pre_topc(X0,X1)
% 2.23/1.04      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.23/1.04      | ~ l1_pre_topc(X1) ),
% 2.23/1.04      inference(cnf_transformation,[],[f50]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_677,plain,
% 2.23/1.04      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.23/1.04      | ~ l1_pre_topc(X1)
% 2.23/1.04      | sK3 != X1
% 2.23/1.04      | sK5 != X0 ),
% 2.23/1.04      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_678,plain,
% 2.23/1.04      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.23/1.04      | ~ l1_pre_topc(sK3) ),
% 2.23/1.04      inference(unflattening,[status(thm)],[c_677]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_14,negated_conjecture,
% 2.23/1.04      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.23/1.04      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 2.23/1.04      inference(cnf_transformation,[],[f73]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_15,negated_conjecture,
% 2.23/1.04      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.23/1.04      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 2.23/1.04      inference(cnf_transformation,[],[f72]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_17,negated_conjecture,
% 2.23/1.04      ( r1_tarski(sK6,u1_struct_0(sK5)) ),
% 2.23/1.04      inference(cnf_transformation,[],[f70]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_18,negated_conjecture,
% 2.23/1.04      ( r2_hidden(sK7,sK6) ),
% 2.23/1.04      inference(cnf_transformation,[],[f69]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_19,negated_conjecture,
% 2.23/1.04      ( v3_pre_topc(sK6,sK3) ),
% 2.23/1.04      inference(cnf_transformation,[],[f68]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_20,negated_conjecture,
% 2.23/1.04      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 2.23/1.04      inference(cnf_transformation,[],[f67]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_21,negated_conjecture,
% 2.23/1.04      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.23/1.04      inference(cnf_transformation,[],[f66]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(c_22,negated_conjecture,
% 2.23/1.04      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.23/1.04      inference(cnf_transformation,[],[f65]) ).
% 2.23/1.04  
% 2.23/1.04  cnf(contradiction,plain,
% 2.23/1.04      ( $false ),
% 2.23/1.04      inference(minisat,
% 2.23/1.04                [status(thm)],
% 2.23/1.04                [c_5699,c_5563,c_4824,c_4790,c_4792,c_4757,c_4654,c_4645,
% 2.23/1.04                 c_4644,c_4571,c_4512,c_4418,c_3164,c_678,c_14,c_15,c_17,
% 2.23/1.04                 c_18,c_19,c_20,c_21,c_22,c_28]) ).
% 2.23/1.04  
% 2.23/1.04  
% 2.23/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.23/1.04  
% 2.23/1.04  ------                               Statistics
% 2.23/1.04  
% 2.23/1.04  ------ General
% 2.23/1.04  
% 2.23/1.04  abstr_ref_over_cycles:                  0
% 2.23/1.04  abstr_ref_under_cycles:                 0
% 2.23/1.04  gc_basic_clause_elim:                   0
% 2.23/1.04  forced_gc_time:                         0
% 2.23/1.04  parsing_time:                           0.009
% 2.23/1.04  unif_index_cands_time:                  0.
% 2.23/1.04  unif_index_add_time:                    0.
% 2.23/1.04  orderings_time:                         0.
% 2.23/1.04  out_proof_time:                         0.015
% 2.23/1.04  total_time:                             0.189
% 2.23/1.04  num_of_symbols:                         60
% 2.23/1.04  num_of_terms:                           3741
% 2.23/1.04  
% 2.23/1.04  ------ Preprocessing
% 2.23/1.04  
% 2.23/1.04  num_of_splits:                          2
% 2.23/1.04  num_of_split_atoms:                     2
% 2.23/1.04  num_of_reused_defs:                     0
% 2.23/1.04  num_eq_ax_congr_red:                    23
% 2.23/1.04  num_of_sem_filtered_clauses:            1
% 2.23/1.04  num_of_subtypes:                        2
% 2.23/1.04  monotx_restored_types:                  0
% 2.23/1.04  sat_num_of_epr_types:                   0
% 2.23/1.04  sat_num_of_non_cyclic_types:            0
% 2.23/1.04  sat_guarded_non_collapsed_types:        0
% 2.23/1.04  num_pure_diseq_elim:                    0
% 2.23/1.04  simp_replaced_by:                       0
% 2.23/1.04  res_preprocessed:                       130
% 2.23/1.04  prep_upred:                             0
% 2.23/1.04  prep_unflattend:                        113
% 2.23/1.04  smt_new_axioms:                         0
% 2.23/1.04  pred_elim_cands:                        12
% 2.23/1.04  pred_elim:                              6
% 2.23/1.04  pred_elim_cl:                           -2
% 2.23/1.04  pred_elim_cycles:                       12
% 2.23/1.04  merged_defs:                            6
% 2.23/1.04  merged_defs_ncl:                        0
% 2.23/1.04  bin_hyper_res:                          6
% 2.23/1.04  prep_cycles:                            3
% 2.23/1.04  pred_elim_time:                         0.071
% 2.23/1.04  splitting_time:                         0.
% 2.23/1.04  sem_filter_time:                        0.
% 2.23/1.04  monotx_time:                            0.
% 2.23/1.04  subtype_inf_time:                       0.
% 2.23/1.04  
% 2.23/1.04  ------ Problem properties
% 2.23/1.04  
% 2.23/1.04  clauses:                                37
% 2.23/1.04  conjectures:                            10
% 2.23/1.04  epr:                                    3
% 2.23/1.04  horn:                                   36
% 2.23/1.04  ground:                                 13
% 2.23/1.04  unary:                                  9
% 2.23/1.04  binary:                                 2
% 2.23/1.04  lits:                                   111
% 2.23/1.04  lits_eq:                                5
% 2.23/1.04  fd_pure:                                0
% 2.23/1.04  fd_pseudo:                              0
% 2.23/1.04  fd_cond:                                0
% 2.23/1.04  fd_pseudo_cond:                         0
% 2.23/1.04  ac_symbols:                             0
% 2.23/1.04  
% 2.23/1.04  ------ Propositional Solver
% 2.23/1.04  
% 2.23/1.04  prop_solver_calls:                      22
% 2.23/1.04  prop_fast_solver_calls:                 1892
% 2.23/1.04  smt_solver_calls:                       0
% 2.23/1.04  smt_fast_solver_calls:                  0
% 2.23/1.04  prop_num_of_clauses:                    1270
% 2.23/1.04  prop_preprocess_simplified:             4642
% 2.23/1.04  prop_fo_subsumed:                       107
% 2.23/1.04  prop_solver_time:                       0.
% 2.23/1.04  smt_solver_time:                        0.
% 2.23/1.04  smt_fast_solver_time:                   0.
% 2.23/1.04  prop_fast_solver_time:                  0.
% 2.23/1.04  prop_unsat_core_time:                   0.
% 2.23/1.04  
% 2.23/1.04  ------ QBF
% 2.23/1.04  
% 2.23/1.04  qbf_q_res:                              0
% 2.23/1.04  qbf_num_tautologies:                    0
% 2.23/1.04  qbf_prep_cycles:                        0
% 2.23/1.04  
% 2.23/1.04  ------ BMC1
% 2.23/1.04  
% 2.23/1.04  bmc1_current_bound:                     -1
% 2.23/1.04  bmc1_last_solved_bound:                 -1
% 2.23/1.04  bmc1_unsat_core_size:                   -1
% 2.23/1.04  bmc1_unsat_core_parents_size:           -1
% 2.23/1.04  bmc1_merge_next_fun:                    0
% 2.23/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.23/1.04  
% 2.23/1.04  ------ Instantiation
% 2.23/1.04  
% 2.23/1.04  inst_num_of_clauses:                    250
% 2.23/1.04  inst_num_in_passive:                    17
% 2.23/1.04  inst_num_in_active:                     194
% 2.23/1.04  inst_num_in_unprocessed:                38
% 2.23/1.04  inst_num_of_loops:                      204
% 2.23/1.04  inst_num_of_learning_restarts:          0
% 2.23/1.04  inst_num_moves_active_passive:          4
% 2.23/1.04  inst_lit_activity:                      0
% 2.23/1.04  inst_lit_activity_moves:                0
% 2.23/1.04  inst_num_tautologies:                   0
% 2.23/1.04  inst_num_prop_implied:                  0
% 2.23/1.04  inst_num_existing_simplified:           0
% 2.23/1.04  inst_num_eq_res_simplified:             0
% 2.23/1.04  inst_num_child_elim:                    0
% 2.23/1.04  inst_num_of_dismatching_blockings:      10
% 2.23/1.04  inst_num_of_non_proper_insts:           215
% 2.23/1.04  inst_num_of_duplicates:                 0
% 2.23/1.04  inst_inst_num_from_inst_to_res:         0
% 2.23/1.04  inst_dismatching_checking_time:         0.
% 2.23/1.04  
% 2.23/1.04  ------ Resolution
% 2.23/1.04  
% 2.23/1.04  res_num_of_clauses:                     0
% 2.23/1.04  res_num_in_passive:                     0
% 2.23/1.04  res_num_in_active:                      0
% 2.23/1.04  res_num_of_loops:                       133
% 2.23/1.04  res_forward_subset_subsumed:            62
% 2.23/1.04  res_backward_subset_subsumed:           2
% 2.23/1.04  res_forward_subsumed:                   0
% 2.23/1.04  res_backward_subsumed:                  0
% 2.23/1.04  res_forward_subsumption_resolution:     1
% 2.23/1.04  res_backward_subsumption_resolution:    0
% 2.23/1.04  res_clause_to_clause_subsumption:       177
% 2.23/1.04  res_orphan_elimination:                 0
% 2.23/1.04  res_tautology_del:                      50
% 2.23/1.04  res_num_eq_res_simplified:              2
% 2.23/1.04  res_num_sel_changes:                    0
% 2.23/1.04  res_moves_from_active_to_pass:          0
% 2.23/1.04  
% 2.23/1.04  ------ Superposition
% 2.23/1.04  
% 2.23/1.04  sup_time_total:                         0.
% 2.23/1.04  sup_time_generating:                    0.
% 2.23/1.04  sup_time_sim_full:                      0.
% 2.23/1.04  sup_time_sim_immed:                     0.
% 2.23/1.04  
% 2.23/1.04  sup_num_of_clauses:                     51
% 2.23/1.04  sup_num_in_active:                      40
% 2.23/1.04  sup_num_in_passive:                     11
% 2.23/1.04  sup_num_of_loops:                       40
% 2.23/1.04  sup_fw_superposition:                   14
% 2.23/1.04  sup_bw_superposition:                   3
% 2.23/1.04  sup_immediate_simplified:               1
% 2.23/1.04  sup_given_eliminated:                   0
% 2.23/1.04  comparisons_done:                       0
% 2.23/1.04  comparisons_avoided:                    0
% 2.23/1.04  
% 2.23/1.04  ------ Simplifications
% 2.23/1.04  
% 2.23/1.04  
% 2.23/1.04  sim_fw_subset_subsumed:                 1
% 2.23/1.04  sim_bw_subset_subsumed:                 0
% 2.23/1.04  sim_fw_subsumed:                        0
% 2.23/1.04  sim_bw_subsumed:                        0
% 2.23/1.04  sim_fw_subsumption_res:                 0
% 2.23/1.04  sim_bw_subsumption_res:                 0
% 2.23/1.04  sim_tautology_del:                      1
% 2.23/1.04  sim_eq_tautology_del:                   0
% 2.23/1.04  sim_eq_res_simp:                        2
% 2.23/1.04  sim_fw_demodulated:                     0
% 2.23/1.04  sim_bw_demodulated:                     0
% 2.23/1.04  sim_light_normalised:                   4
% 2.23/1.04  sim_joinable_taut:                      0
% 2.23/1.04  sim_joinable_simp:                      0
% 2.23/1.04  sim_ac_normalised:                      0
% 2.23/1.04  sim_smt_subsumption:                    0
% 2.23/1.04  
%------------------------------------------------------------------------------
