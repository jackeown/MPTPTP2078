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
% DateTime   : Thu Dec  3 12:22:39 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 867 expanded)
%              Number of clauses        :  111 ( 139 expanded)
%              Number of leaves         :   20 ( 380 expanded)
%              Depth                    :   25
%              Number of atoms          : 1504 (16980 expanded)
%              Number of equality atoms :  130 (1062 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
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
    inference(equality_resolution,[],[f52])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
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

cnf(c_733,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_26])).

cnf(c_734,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_733])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_738,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_connsp_2(X4,X2,X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_734,c_27])).

cnf(c_739,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_738])).

cnf(c_864,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_739])).

cnf(c_865,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
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
    inference(unflattening,[status(thm)],[c_864])).

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

cnf(c_869,plain,
    ( ~ l1_pre_topc(X0)
    | r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_865,c_30,c_29,c_28,c_24])).

cnf(c_870,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_869])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1374,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_870,c_31])).

cnf(c_1375,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1374])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1379,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | r1_tmap_1(sK3,sK2,sK4,X0)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1375,c_33,c_32,c_25])).

cnf(c_1380,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1379])).

cnf(c_3368,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_53)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_53)
    | ~ m1_connsp_2(X1_53,sK3,X0_53)
    | ~ r1_tarski(X1_53,u1_struct_0(sK5))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_1380])).

cnf(c_3558,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_53)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_53)
    | ~ m1_connsp_2(X1_53,sK3,X0_53)
    | ~ r1_tarski(X1_53,u1_struct_0(sK5))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(equality_resolution_simp,[status(thm)],[c_3368])).

cnf(c_5300,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_53)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_53)
    | ~ m1_connsp_2(sK0(sK3,sK7,u1_struct_0(sK5)),sK3,X0_53)
    | ~ r1_tarski(sK0(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK5))
    | ~ m1_subset_1(sK0(sK3,sK7,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3558])).

cnf(c_6136,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_connsp_2(sK0(sK3,sK7,u1_struct_0(sK5)),sK3,sK7)
    | ~ r1_tarski(sK0(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5))
    | ~ m1_subset_1(sK0(sK3,sK7,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_5300])).

cnf(c_3398,plain,
    ( ~ r1_tmap_1(X0_54,X1_54,X0_53,X1_53)
    | r1_tmap_1(X0_54,X1_54,X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_4703,plain,
    ( r1_tmap_1(sK5,sK2,X0_53,X1_53)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | X0_53 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | X1_53 != sK7 ),
    inference(instantiation,[status(thm)],[c_3398])).

cnf(c_5388,plain,
    ( r1_tmap_1(sK5,sK2,X0_53,sK8)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | X0_53 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK8 != sK7 ),
    inference(instantiation,[status(thm)],[c_4703])).

cnf(c_5803,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK8 != sK7 ),
    inference(instantiation,[status(thm)],[c_5388])).

cnf(c_3390,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_4818,plain,
    ( X0_53 != X1_53
    | X0_53 = sK7
    | sK7 != X1_53 ),
    inference(instantiation,[status(thm)],[c_3390])).

cnf(c_4970,plain,
    ( X0_53 = sK7
    | X0_53 != sK8
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_4818])).

cnf(c_5041,plain,
    ( sK7 != sK8
    | sK8 = sK7
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_4970])).

cnf(c_1,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1613,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_28])).

cnf(c_1614,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | r1_tarski(sK0(sK3,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1613])).

cnf(c_1618,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | r1_tarski(sK0(sK3,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1614,c_30,c_29])).

cnf(c_3359,plain,
    ( ~ m1_connsp_2(X0_53,sK3,X1_53)
    | r1_tarski(sK0(sK3,X1_53,X0_53),X0_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1618])).

cnf(c_4610,plain,
    ( ~ m1_connsp_2(X0_53,sK3,sK7)
    | r1_tarski(sK0(sK3,sK7,X0_53),X0_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3359])).

cnf(c_5007,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
    | r1_tarski(sK0(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4610])).

cnf(c_3,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1565,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_28])).

cnf(c_1566,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | m1_connsp_2(sK0(sK3,X1,X0),sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1565])).

cnf(c_1570,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | m1_connsp_2(sK0(sK3,X1,X0),sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1566,c_30,c_29])).

cnf(c_3361,plain,
    ( ~ m1_connsp_2(X0_53,sK3,X1_53)
    | m1_connsp_2(sK0(sK3,X1_53,X0_53),sK3,X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1570])).

cnf(c_4615,plain,
    ( ~ m1_connsp_2(X0_53,sK3,sK7)
    | m1_connsp_2(sK0(sK3,sK7,X0_53),sK3,sK7)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3361])).

cnf(c_5009,plain,
    ( m1_connsp_2(sK0(sK3,sK7,u1_struct_0(sK5)),sK3,sK7)
    | ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4615])).

cnf(c_4,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1541,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_28])).

cnf(c_1542,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK0(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1541])).

cnf(c_1546,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK0(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1542,c_30,c_29])).

cnf(c_3362,plain,
    ( ~ m1_connsp_2(X0_53,sK3,X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK0(sK3,X1_53,X0_53),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1546])).

cnf(c_4591,plain,
    ( ~ m1_connsp_2(X0_53,sK3,sK7)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK0(sK3,sK7,X0_53),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3362])).

cnf(c_5012,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
    | m1_subset_1(sK0(sK3,sK7,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4591])).

cnf(c_5,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ r1_tarski(X3,X0)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1506,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ r1_tarski(X3,X0)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_28])).

cnf(c_1507,plain,
    ( m1_connsp_2(X0,sK3,X1)
    | ~ v3_pre_topc(X2,sK3)
    | ~ r1_tarski(X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1506])).

cnf(c_1511,plain,
    ( m1_connsp_2(X0,sK3,X1)
    | ~ v3_pre_topc(X2,sK3)
    | ~ r1_tarski(X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1507,c_30,c_29])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1531,plain,
    ( m1_connsp_2(X0,sK3,X1)
    | ~ v3_pre_topc(X2,sK3)
    | ~ r1_tarski(X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1511,c_0])).

cnf(c_3363,plain,
    ( m1_connsp_2(X0_53,sK3,X1_53)
    | ~ v3_pre_topc(X2_53,sK3)
    | ~ r1_tarski(X2_53,X0_53)
    | ~ r2_hidden(X1_53,X2_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2_53,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1531])).

cnf(c_4642,plain,
    ( m1_connsp_2(X0_53,sK3,X1_53)
    | ~ v3_pre_topc(sK6,sK3)
    | ~ r1_tarski(sK6,X0_53)
    | ~ r2_hidden(X1_53,sK6)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3363])).

cnf(c_4881,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,X0_53)
    | ~ v3_pre_topc(sK6,sK3)
    | ~ r1_tarski(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(X0_53,sK6)
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_4642])).

cnf(c_5005,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
    | ~ v3_pre_topc(sK6,sK3)
    | ~ r1_tarski(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(sK7,sK6)
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_4881])).

cnf(c_3389,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_4872,plain,
    ( k2_tmap_1(sK3,sK2,sK4,sK5) = k2_tmap_1(sK3,sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3389])).

cnf(c_4698,plain,
    ( r1_tmap_1(sK5,sK2,X0_53,X1_53)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | X0_53 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | X1_53 != sK8 ),
    inference(instantiation,[status(thm)],[c_3398])).

cnf(c_4839,plain,
    ( r1_tmap_1(sK5,sK2,X0_53,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | X0_53 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_4698])).

cnf(c_4871,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_4839])).

cnf(c_4866,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3389])).

cnf(c_3391,plain,
    ( ~ m1_subset_1(X0_53,X1_53)
    | m1_subset_1(X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_4663,plain,
    ( m1_subset_1(X0_53,X1_53)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | X1_53 != u1_struct_0(sK5)
    | X0_53 != sK8 ),
    inference(instantiation,[status(thm)],[c_3391])).

cnf(c_4791,plain,
    ( m1_subset_1(sK7,X0_53)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | X0_53 != u1_struct_0(sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_4663])).

cnf(c_4865,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_4791])).

cnf(c_4797,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_3389])).

cnf(c_13,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_11,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_181,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_11])).

cnf(c_182,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_181])).

cnf(c_676,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_182,c_26])).

cnf(c_677,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_681,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_677,c_27])).

cnf(c_682,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_681])).

cnf(c_915,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_682])).

cnf(c_916,plain,
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
    inference(unflattening,[status(thm)],[c_915])).

cnf(c_920,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_916,c_30,c_29,c_28,c_24])).

cnf(c_921,plain,
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
    inference(renaming,[status(thm)],[c_920])).

cnf(c_1347,plain,
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
    inference(resolution_lifted,[status(thm)],[c_921,c_31])).

cnf(c_1348,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1347])).

cnf(c_1352,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1348,c_33,c_32,c_25])).

cnf(c_1353,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1352])).

cnf(c_3369,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0_53)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_1353])).

cnf(c_3554,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0_53)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_3369])).

cnf(c_4634,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3554])).

cnf(c_16,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3380,negated_conjecture,
    ( sK7 = sK8 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_853,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_854,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_853])).

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
    inference(minisat,[status(thm)],[c_6136,c_5803,c_5041,c_5007,c_5009,c_5012,c_5005,c_4872,c_4871,c_4866,c_4865,c_4797,c_4634,c_3380,c_854,c_14,c_15,c_17,c_18,c_19,c_20,c_21,c_22,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:19:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.27/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/0.96  
% 2.27/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.27/0.96  
% 2.27/0.96  ------  iProver source info
% 2.27/0.96  
% 2.27/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.27/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.27/0.96  git: non_committed_changes: false
% 2.27/0.96  git: last_make_outside_of_git: false
% 2.27/0.96  
% 2.27/0.96  ------ 
% 2.27/0.96  
% 2.27/0.96  ------ Input Options
% 2.27/0.96  
% 2.27/0.96  --out_options                           all
% 2.27/0.96  --tptp_safe_out                         true
% 2.27/0.96  --problem_path                          ""
% 2.27/0.96  --include_path                          ""
% 2.27/0.96  --clausifier                            res/vclausify_rel
% 2.27/0.96  --clausifier_options                    --mode clausify
% 2.27/0.96  --stdin                                 false
% 2.27/0.96  --stats_out                             all
% 2.27/0.96  
% 2.27/0.96  ------ General Options
% 2.27/0.96  
% 2.27/0.96  --fof                                   false
% 2.27/0.96  --time_out_real                         305.
% 2.27/0.96  --time_out_virtual                      -1.
% 2.27/0.96  --symbol_type_check                     false
% 2.27/0.96  --clausify_out                          false
% 2.27/0.96  --sig_cnt_out                           false
% 2.27/0.96  --trig_cnt_out                          false
% 2.27/0.96  --trig_cnt_out_tolerance                1.
% 2.27/0.96  --trig_cnt_out_sk_spl                   false
% 2.27/0.96  --abstr_cl_out                          false
% 2.27/0.96  
% 2.27/0.96  ------ Global Options
% 2.27/0.96  
% 2.27/0.96  --schedule                              default
% 2.27/0.96  --add_important_lit                     false
% 2.27/0.96  --prop_solver_per_cl                    1000
% 2.27/0.96  --min_unsat_core                        false
% 2.27/0.96  --soft_assumptions                      false
% 2.27/0.96  --soft_lemma_size                       3
% 2.27/0.96  --prop_impl_unit_size                   0
% 2.27/0.96  --prop_impl_unit                        []
% 2.27/0.96  --share_sel_clauses                     true
% 2.27/0.96  --reset_solvers                         false
% 2.27/0.96  --bc_imp_inh                            [conj_cone]
% 2.27/0.96  --conj_cone_tolerance                   3.
% 2.27/0.96  --extra_neg_conj                        none
% 2.27/0.96  --large_theory_mode                     true
% 2.27/0.96  --prolific_symb_bound                   200
% 2.27/0.96  --lt_threshold                          2000
% 2.27/0.96  --clause_weak_htbl                      true
% 2.27/0.96  --gc_record_bc_elim                     false
% 2.27/0.96  
% 2.27/0.96  ------ Preprocessing Options
% 2.27/0.96  
% 2.27/0.96  --preprocessing_flag                    true
% 2.27/0.96  --time_out_prep_mult                    0.1
% 2.27/0.96  --splitting_mode                        input
% 2.27/0.96  --splitting_grd                         true
% 2.27/0.96  --splitting_cvd                         false
% 2.27/0.96  --splitting_cvd_svl                     false
% 2.27/0.96  --splitting_nvd                         32
% 2.27/0.96  --sub_typing                            true
% 2.27/0.96  --prep_gs_sim                           true
% 2.27/0.96  --prep_unflatten                        true
% 2.27/0.96  --prep_res_sim                          true
% 2.27/0.96  --prep_upred                            true
% 2.27/0.96  --prep_sem_filter                       exhaustive
% 2.27/0.96  --prep_sem_filter_out                   false
% 2.27/0.96  --pred_elim                             true
% 2.27/0.96  --res_sim_input                         true
% 2.27/0.96  --eq_ax_congr_red                       true
% 2.27/0.96  --pure_diseq_elim                       true
% 2.27/0.96  --brand_transform                       false
% 2.27/0.96  --non_eq_to_eq                          false
% 2.27/0.96  --prep_def_merge                        true
% 2.27/0.96  --prep_def_merge_prop_impl              false
% 2.27/0.96  --prep_def_merge_mbd                    true
% 2.27/0.96  --prep_def_merge_tr_red                 false
% 2.27/0.96  --prep_def_merge_tr_cl                  false
% 2.27/0.96  --smt_preprocessing                     true
% 2.27/0.96  --smt_ac_axioms                         fast
% 2.27/0.96  --preprocessed_out                      false
% 2.27/0.96  --preprocessed_stats                    false
% 2.27/0.96  
% 2.27/0.96  ------ Abstraction refinement Options
% 2.27/0.96  
% 2.27/0.96  --abstr_ref                             []
% 2.27/0.96  --abstr_ref_prep                        false
% 2.27/0.96  --abstr_ref_until_sat                   false
% 2.27/0.96  --abstr_ref_sig_restrict                funpre
% 2.27/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/0.96  --abstr_ref_under                       []
% 2.27/0.96  
% 2.27/0.96  ------ SAT Options
% 2.27/0.96  
% 2.27/0.96  --sat_mode                              false
% 2.27/0.96  --sat_fm_restart_options                ""
% 2.27/0.96  --sat_gr_def                            false
% 2.27/0.96  --sat_epr_types                         true
% 2.27/0.96  --sat_non_cyclic_types                  false
% 2.27/0.96  --sat_finite_models                     false
% 2.27/0.96  --sat_fm_lemmas                         false
% 2.27/0.96  --sat_fm_prep                           false
% 2.27/0.97  --sat_fm_uc_incr                        true
% 2.27/0.97  --sat_out_model                         small
% 2.27/0.97  --sat_out_clauses                       false
% 2.27/0.97  
% 2.27/0.97  ------ QBF Options
% 2.27/0.97  
% 2.27/0.97  --qbf_mode                              false
% 2.27/0.97  --qbf_elim_univ                         false
% 2.27/0.97  --qbf_dom_inst                          none
% 2.27/0.97  --qbf_dom_pre_inst                      false
% 2.27/0.97  --qbf_sk_in                             false
% 2.27/0.97  --qbf_pred_elim                         true
% 2.27/0.97  --qbf_split                             512
% 2.27/0.97  
% 2.27/0.97  ------ BMC1 Options
% 2.27/0.97  
% 2.27/0.97  --bmc1_incremental                      false
% 2.27/0.97  --bmc1_axioms                           reachable_all
% 2.27/0.97  --bmc1_min_bound                        0
% 2.27/0.97  --bmc1_max_bound                        -1
% 2.27/0.97  --bmc1_max_bound_default                -1
% 2.27/0.97  --bmc1_symbol_reachability              true
% 2.27/0.97  --bmc1_property_lemmas                  false
% 2.27/0.97  --bmc1_k_induction                      false
% 2.27/0.97  --bmc1_non_equiv_states                 false
% 2.27/0.97  --bmc1_deadlock                         false
% 2.27/0.97  --bmc1_ucm                              false
% 2.27/0.97  --bmc1_add_unsat_core                   none
% 2.27/0.97  --bmc1_unsat_core_children              false
% 2.27/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/0.97  --bmc1_out_stat                         full
% 2.27/0.97  --bmc1_ground_init                      false
% 2.27/0.97  --bmc1_pre_inst_next_state              false
% 2.27/0.97  --bmc1_pre_inst_state                   false
% 2.27/0.97  --bmc1_pre_inst_reach_state             false
% 2.27/0.97  --bmc1_out_unsat_core                   false
% 2.27/0.97  --bmc1_aig_witness_out                  false
% 2.27/0.97  --bmc1_verbose                          false
% 2.27/0.97  --bmc1_dump_clauses_tptp                false
% 2.27/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.27/0.97  --bmc1_dump_file                        -
% 2.27/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.27/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.27/0.97  --bmc1_ucm_extend_mode                  1
% 2.27/0.97  --bmc1_ucm_init_mode                    2
% 2.27/0.97  --bmc1_ucm_cone_mode                    none
% 2.27/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.27/0.97  --bmc1_ucm_relax_model                  4
% 2.27/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.27/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/0.97  --bmc1_ucm_layered_model                none
% 2.27/0.97  --bmc1_ucm_max_lemma_size               10
% 2.27/0.97  
% 2.27/0.97  ------ AIG Options
% 2.27/0.97  
% 2.27/0.97  --aig_mode                              false
% 2.27/0.97  
% 2.27/0.97  ------ Instantiation Options
% 2.27/0.97  
% 2.27/0.97  --instantiation_flag                    true
% 2.27/0.97  --inst_sos_flag                         false
% 2.27/0.97  --inst_sos_phase                        true
% 2.27/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/0.97  --inst_lit_sel_side                     num_symb
% 2.27/0.97  --inst_solver_per_active                1400
% 2.27/0.97  --inst_solver_calls_frac                1.
% 2.27/0.97  --inst_passive_queue_type               priority_queues
% 2.27/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/0.97  --inst_passive_queues_freq              [25;2]
% 2.27/0.97  --inst_dismatching                      true
% 2.27/0.97  --inst_eager_unprocessed_to_passive     true
% 2.27/0.97  --inst_prop_sim_given                   true
% 2.27/0.97  --inst_prop_sim_new                     false
% 2.27/0.97  --inst_subs_new                         false
% 2.27/0.97  --inst_eq_res_simp                      false
% 2.27/0.97  --inst_subs_given                       false
% 2.27/0.97  --inst_orphan_elimination               true
% 2.27/0.97  --inst_learning_loop_flag               true
% 2.27/0.97  --inst_learning_start                   3000
% 2.27/0.97  --inst_learning_factor                  2
% 2.27/0.97  --inst_start_prop_sim_after_learn       3
% 2.27/0.97  --inst_sel_renew                        solver
% 2.27/0.97  --inst_lit_activity_flag                true
% 2.27/0.97  --inst_restr_to_given                   false
% 2.27/0.97  --inst_activity_threshold               500
% 2.27/0.97  --inst_out_proof                        true
% 2.27/0.97  
% 2.27/0.97  ------ Resolution Options
% 2.27/0.97  
% 2.27/0.97  --resolution_flag                       true
% 2.27/0.97  --res_lit_sel                           adaptive
% 2.27/0.97  --res_lit_sel_side                      none
% 2.27/0.97  --res_ordering                          kbo
% 2.27/0.97  --res_to_prop_solver                    active
% 2.27/0.97  --res_prop_simpl_new                    false
% 2.27/0.97  --res_prop_simpl_given                  true
% 2.27/0.97  --res_passive_queue_type                priority_queues
% 2.27/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/0.97  --res_passive_queues_freq               [15;5]
% 2.27/0.97  --res_forward_subs                      full
% 2.27/0.97  --res_backward_subs                     full
% 2.27/0.97  --res_forward_subs_resolution           true
% 2.27/0.97  --res_backward_subs_resolution          true
% 2.27/0.97  --res_orphan_elimination                true
% 2.27/0.97  --res_time_limit                        2.
% 2.27/0.97  --res_out_proof                         true
% 2.27/0.97  
% 2.27/0.97  ------ Superposition Options
% 2.27/0.97  
% 2.27/0.97  --superposition_flag                    true
% 2.27/0.97  --sup_passive_queue_type                priority_queues
% 2.27/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.27/0.97  --demod_completeness_check              fast
% 2.27/0.97  --demod_use_ground                      true
% 2.27/0.97  --sup_to_prop_solver                    passive
% 2.27/0.97  --sup_prop_simpl_new                    true
% 2.27/0.97  --sup_prop_simpl_given                  true
% 2.27/0.97  --sup_fun_splitting                     false
% 2.27/0.97  --sup_smt_interval                      50000
% 2.27/0.97  
% 2.27/0.97  ------ Superposition Simplification Setup
% 2.27/0.97  
% 2.27/0.97  --sup_indices_passive                   []
% 2.27/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.97  --sup_full_bw                           [BwDemod]
% 2.27/0.97  --sup_immed_triv                        [TrivRules]
% 2.27/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.97  --sup_immed_bw_main                     []
% 2.27/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.97  
% 2.27/0.97  ------ Combination Options
% 2.27/0.97  
% 2.27/0.97  --comb_res_mult                         3
% 2.27/0.97  --comb_sup_mult                         2
% 2.27/0.97  --comb_inst_mult                        10
% 2.27/0.97  
% 2.27/0.97  ------ Debug Options
% 2.27/0.97  
% 2.27/0.97  --dbg_backtrace                         false
% 2.27/0.97  --dbg_dump_prop_clauses                 false
% 2.27/0.97  --dbg_dump_prop_clauses_file            -
% 2.27/0.97  --dbg_out_stat                          false
% 2.27/0.97  ------ Parsing...
% 2.27/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.27/0.97  
% 2.27/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 2.27/0.97  
% 2.27/0.97  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.27/0.97  
% 2.27/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.27/0.97  ------ Proving...
% 2.27/0.97  ------ Problem Properties 
% 2.27/0.97  
% 2.27/0.97  
% 2.27/0.97  clauses                                 36
% 2.27/0.97  conjectures                             10
% 2.27/0.97  EPR                                     3
% 2.27/0.97  Horn                                    35
% 2.27/0.97  unary                                   9
% 2.27/0.97  binary                                  2
% 2.27/0.97  lits                                    124
% 2.27/0.97  lits eq                                 5
% 2.27/0.97  fd_pure                                 0
% 2.27/0.97  fd_pseudo                               0
% 2.27/0.97  fd_cond                                 0
% 2.27/0.97  fd_pseudo_cond                          0
% 2.27/0.97  AC symbols                              0
% 2.27/0.97  
% 2.27/0.97  ------ Schedule dynamic 5 is on 
% 2.27/0.97  
% 2.27/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.27/0.97  
% 2.27/0.97  
% 2.27/0.97  ------ 
% 2.27/0.97  Current options:
% 2.27/0.97  ------ 
% 2.27/0.97  
% 2.27/0.97  ------ Input Options
% 2.27/0.97  
% 2.27/0.97  --out_options                           all
% 2.27/0.97  --tptp_safe_out                         true
% 2.27/0.97  --problem_path                          ""
% 2.27/0.97  --include_path                          ""
% 2.27/0.97  --clausifier                            res/vclausify_rel
% 2.27/0.97  --clausifier_options                    --mode clausify
% 2.27/0.97  --stdin                                 false
% 2.27/0.97  --stats_out                             all
% 2.27/0.97  
% 2.27/0.97  ------ General Options
% 2.27/0.97  
% 2.27/0.97  --fof                                   false
% 2.27/0.97  --time_out_real                         305.
% 2.27/0.97  --time_out_virtual                      -1.
% 2.27/0.97  --symbol_type_check                     false
% 2.27/0.97  --clausify_out                          false
% 2.27/0.97  --sig_cnt_out                           false
% 2.27/0.97  --trig_cnt_out                          false
% 2.27/0.97  --trig_cnt_out_tolerance                1.
% 2.27/0.97  --trig_cnt_out_sk_spl                   false
% 2.27/0.97  --abstr_cl_out                          false
% 2.27/0.97  
% 2.27/0.97  ------ Global Options
% 2.27/0.97  
% 2.27/0.97  --schedule                              default
% 2.27/0.97  --add_important_lit                     false
% 2.27/0.97  --prop_solver_per_cl                    1000
% 2.27/0.97  --min_unsat_core                        false
% 2.27/0.97  --soft_assumptions                      false
% 2.27/0.97  --soft_lemma_size                       3
% 2.27/0.97  --prop_impl_unit_size                   0
% 2.27/0.97  --prop_impl_unit                        []
% 2.27/0.97  --share_sel_clauses                     true
% 2.27/0.97  --reset_solvers                         false
% 2.27/0.97  --bc_imp_inh                            [conj_cone]
% 2.27/0.97  --conj_cone_tolerance                   3.
% 2.27/0.97  --extra_neg_conj                        none
% 2.27/0.97  --large_theory_mode                     true
% 2.27/0.97  --prolific_symb_bound                   200
% 2.27/0.97  --lt_threshold                          2000
% 2.27/0.97  --clause_weak_htbl                      true
% 2.27/0.97  --gc_record_bc_elim                     false
% 2.27/0.97  
% 2.27/0.97  ------ Preprocessing Options
% 2.27/0.97  
% 2.27/0.97  --preprocessing_flag                    true
% 2.27/0.97  --time_out_prep_mult                    0.1
% 2.27/0.97  --splitting_mode                        input
% 2.27/0.97  --splitting_grd                         true
% 2.27/0.97  --splitting_cvd                         false
% 2.27/0.97  --splitting_cvd_svl                     false
% 2.27/0.97  --splitting_nvd                         32
% 2.27/0.97  --sub_typing                            true
% 2.27/0.97  --prep_gs_sim                           true
% 2.27/0.97  --prep_unflatten                        true
% 2.27/0.97  --prep_res_sim                          true
% 2.27/0.97  --prep_upred                            true
% 2.27/0.97  --prep_sem_filter                       exhaustive
% 2.27/0.97  --prep_sem_filter_out                   false
% 2.27/0.97  --pred_elim                             true
% 2.27/0.97  --res_sim_input                         true
% 2.27/0.97  --eq_ax_congr_red                       true
% 2.27/0.97  --pure_diseq_elim                       true
% 2.27/0.97  --brand_transform                       false
% 2.27/0.97  --non_eq_to_eq                          false
% 2.27/0.97  --prep_def_merge                        true
% 2.27/0.97  --prep_def_merge_prop_impl              false
% 2.27/0.97  --prep_def_merge_mbd                    true
% 2.27/0.97  --prep_def_merge_tr_red                 false
% 2.27/0.97  --prep_def_merge_tr_cl                  false
% 2.27/0.97  --smt_preprocessing                     true
% 2.27/0.97  --smt_ac_axioms                         fast
% 2.27/0.97  --preprocessed_out                      false
% 2.27/0.97  --preprocessed_stats                    false
% 2.27/0.97  
% 2.27/0.97  ------ Abstraction refinement Options
% 2.27/0.97  
% 2.27/0.97  --abstr_ref                             []
% 2.27/0.97  --abstr_ref_prep                        false
% 2.27/0.97  --abstr_ref_until_sat                   false
% 2.27/0.97  --abstr_ref_sig_restrict                funpre
% 2.27/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/0.97  --abstr_ref_under                       []
% 2.27/0.97  
% 2.27/0.97  ------ SAT Options
% 2.27/0.97  
% 2.27/0.97  --sat_mode                              false
% 2.27/0.97  --sat_fm_restart_options                ""
% 2.27/0.97  --sat_gr_def                            false
% 2.27/0.97  --sat_epr_types                         true
% 2.27/0.97  --sat_non_cyclic_types                  false
% 2.27/0.97  --sat_finite_models                     false
% 2.27/0.97  --sat_fm_lemmas                         false
% 2.27/0.97  --sat_fm_prep                           false
% 2.27/0.97  --sat_fm_uc_incr                        true
% 2.27/0.97  --sat_out_model                         small
% 2.27/0.97  --sat_out_clauses                       false
% 2.27/0.97  
% 2.27/0.97  ------ QBF Options
% 2.27/0.97  
% 2.27/0.97  --qbf_mode                              false
% 2.27/0.97  --qbf_elim_univ                         false
% 2.27/0.97  --qbf_dom_inst                          none
% 2.27/0.97  --qbf_dom_pre_inst                      false
% 2.27/0.97  --qbf_sk_in                             false
% 2.27/0.97  --qbf_pred_elim                         true
% 2.27/0.97  --qbf_split                             512
% 2.27/0.97  
% 2.27/0.97  ------ BMC1 Options
% 2.27/0.97  
% 2.27/0.97  --bmc1_incremental                      false
% 2.27/0.97  --bmc1_axioms                           reachable_all
% 2.27/0.97  --bmc1_min_bound                        0
% 2.27/0.97  --bmc1_max_bound                        -1
% 2.27/0.97  --bmc1_max_bound_default                -1
% 2.27/0.97  --bmc1_symbol_reachability              true
% 2.27/0.97  --bmc1_property_lemmas                  false
% 2.27/0.97  --bmc1_k_induction                      false
% 2.27/0.97  --bmc1_non_equiv_states                 false
% 2.27/0.97  --bmc1_deadlock                         false
% 2.27/0.97  --bmc1_ucm                              false
% 2.27/0.97  --bmc1_add_unsat_core                   none
% 2.27/0.97  --bmc1_unsat_core_children              false
% 2.27/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/0.97  --bmc1_out_stat                         full
% 2.27/0.97  --bmc1_ground_init                      false
% 2.27/0.97  --bmc1_pre_inst_next_state              false
% 2.27/0.97  --bmc1_pre_inst_state                   false
% 2.27/0.97  --bmc1_pre_inst_reach_state             false
% 2.27/0.97  --bmc1_out_unsat_core                   false
% 2.27/0.97  --bmc1_aig_witness_out                  false
% 2.27/0.97  --bmc1_verbose                          false
% 2.27/0.97  --bmc1_dump_clauses_tptp                false
% 2.27/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.27/0.97  --bmc1_dump_file                        -
% 2.27/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.27/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.27/0.97  --bmc1_ucm_extend_mode                  1
% 2.27/0.97  --bmc1_ucm_init_mode                    2
% 2.27/0.97  --bmc1_ucm_cone_mode                    none
% 2.27/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.27/0.97  --bmc1_ucm_relax_model                  4
% 2.27/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.27/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/0.97  --bmc1_ucm_layered_model                none
% 2.27/0.97  --bmc1_ucm_max_lemma_size               10
% 2.27/0.97  
% 2.27/0.97  ------ AIG Options
% 2.27/0.97  
% 2.27/0.97  --aig_mode                              false
% 2.27/0.97  
% 2.27/0.97  ------ Instantiation Options
% 2.27/0.97  
% 2.27/0.97  --instantiation_flag                    true
% 2.27/0.97  --inst_sos_flag                         false
% 2.27/0.97  --inst_sos_phase                        true
% 2.27/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/0.97  --inst_lit_sel_side                     none
% 2.27/0.97  --inst_solver_per_active                1400
% 2.27/0.97  --inst_solver_calls_frac                1.
% 2.27/0.97  --inst_passive_queue_type               priority_queues
% 2.27/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/0.97  --inst_passive_queues_freq              [25;2]
% 2.27/0.97  --inst_dismatching                      true
% 2.27/0.97  --inst_eager_unprocessed_to_passive     true
% 2.27/0.97  --inst_prop_sim_given                   true
% 2.27/0.97  --inst_prop_sim_new                     false
% 2.27/0.97  --inst_subs_new                         false
% 2.27/0.97  --inst_eq_res_simp                      false
% 2.27/0.97  --inst_subs_given                       false
% 2.27/0.97  --inst_orphan_elimination               true
% 2.27/0.97  --inst_learning_loop_flag               true
% 2.27/0.97  --inst_learning_start                   3000
% 2.27/0.97  --inst_learning_factor                  2
% 2.27/0.97  --inst_start_prop_sim_after_learn       3
% 2.27/0.97  --inst_sel_renew                        solver
% 2.27/0.97  --inst_lit_activity_flag                true
% 2.27/0.97  --inst_restr_to_given                   false
% 2.27/0.97  --inst_activity_threshold               500
% 2.27/0.97  --inst_out_proof                        true
% 2.27/0.97  
% 2.27/0.97  ------ Resolution Options
% 2.27/0.97  
% 2.27/0.97  --resolution_flag                       false
% 2.27/0.97  --res_lit_sel                           adaptive
% 2.27/0.97  --res_lit_sel_side                      none
% 2.27/0.97  --res_ordering                          kbo
% 2.27/0.97  --res_to_prop_solver                    active
% 2.27/0.97  --res_prop_simpl_new                    false
% 2.27/0.97  --res_prop_simpl_given                  true
% 2.27/0.97  --res_passive_queue_type                priority_queues
% 2.27/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/0.97  --res_passive_queues_freq               [15;5]
% 2.27/0.97  --res_forward_subs                      full
% 2.27/0.97  --res_backward_subs                     full
% 2.27/0.97  --res_forward_subs_resolution           true
% 2.27/0.97  --res_backward_subs_resolution          true
% 2.27/0.97  --res_orphan_elimination                true
% 2.27/0.97  --res_time_limit                        2.
% 2.27/0.97  --res_out_proof                         true
% 2.27/0.97  
% 2.27/0.97  ------ Superposition Options
% 2.27/0.97  
% 2.27/0.97  --superposition_flag                    true
% 2.27/0.97  --sup_passive_queue_type                priority_queues
% 2.27/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.27/0.97  --demod_completeness_check              fast
% 2.27/0.97  --demod_use_ground                      true
% 2.27/0.97  --sup_to_prop_solver                    passive
% 2.27/0.97  --sup_prop_simpl_new                    true
% 2.27/0.97  --sup_prop_simpl_given                  true
% 2.27/0.97  --sup_fun_splitting                     false
% 2.27/0.97  --sup_smt_interval                      50000
% 2.27/0.97  
% 2.27/0.97  ------ Superposition Simplification Setup
% 2.27/0.97  
% 2.27/0.97  --sup_indices_passive                   []
% 2.27/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.97  --sup_full_bw                           [BwDemod]
% 2.27/0.97  --sup_immed_triv                        [TrivRules]
% 2.27/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.97  --sup_immed_bw_main                     []
% 2.27/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.97  
% 2.27/0.97  ------ Combination Options
% 2.27/0.97  
% 2.27/0.97  --comb_res_mult                         3
% 2.27/0.97  --comb_sup_mult                         2
% 2.27/0.97  --comb_inst_mult                        10
% 2.27/0.97  
% 2.27/0.97  ------ Debug Options
% 2.27/0.97  
% 2.27/0.97  --dbg_backtrace                         false
% 2.27/0.97  --dbg_dump_prop_clauses                 false
% 2.27/0.97  --dbg_dump_prop_clauses_file            -
% 2.27/0.97  --dbg_out_stat                          false
% 2.27/0.97  
% 2.27/0.97  
% 2.27/0.97  
% 2.27/0.97  
% 2.27/0.97  ------ Proving...
% 2.27/0.97  
% 2.27/0.97  
% 2.27/0.97  % SZS status Theorem for theBenchmark.p
% 2.27/0.97  
% 2.27/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.27/0.97  
% 2.27/0.97  fof(f7,conjecture,(
% 2.27/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.27/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/0.97  
% 2.27/0.97  fof(f8,negated_conjecture,(
% 2.27/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.27/0.97    inference(negated_conjecture,[],[f7])).
% 2.27/0.97  
% 2.27/0.97  fof(f21,plain,(
% 2.27/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.27/0.97    inference(ennf_transformation,[],[f8])).
% 2.27/0.97  
% 2.27/0.97  fof(f22,plain,(
% 2.27/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.27/0.97    inference(flattening,[],[f21])).
% 2.27/0.97  
% 2.27/0.97  fof(f30,plain,(
% 2.27/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5))) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.27/0.97    inference(nnf_transformation,[],[f22])).
% 2.27/0.97  
% 2.27/0.97  fof(f31,plain,(
% 2.27/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.27/0.97    inference(flattening,[],[f30])).
% 2.27/0.97  
% 2.27/0.97  fof(f38,plain,(
% 2.27/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8) | r1_tmap_1(X1,X0,X2,X5)) & sK8 = X5 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(sK8,u1_struct_0(X3)))) )),
% 2.27/0.97    introduced(choice_axiom,[])).
% 2.27/0.97  
% 2.27/0.97  fof(f37,plain,(
% 2.27/0.97    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,sK7)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,sK7)) & sK7 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(sK7,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK7,u1_struct_0(X1)))) )),
% 2.27/0.97    introduced(choice_axiom,[])).
% 2.27/0.97  
% 2.27/0.97  fof(f36,plain,(
% 2.27/0.97    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(sK6,u1_struct_0(X3)) & r2_hidden(X5,sK6) & v3_pre_topc(sK6,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 2.27/0.97    introduced(choice_axiom,[])).
% 2.27/0.97  
% 2.27/0.97  fof(f35,plain,(
% 2.27/0.97    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(sK5)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK5,X1) & ~v2_struct_0(sK5))) )),
% 2.27/0.97    introduced(choice_axiom,[])).
% 2.27/0.97  
% 2.27/0.97  fof(f34,plain,(
% 2.27/0.97    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X6) | ~r1_tmap_1(X1,X0,sK4,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X6) | r1_tmap_1(X1,X0,sK4,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 2.27/0.97    introduced(choice_axiom,[])).
% 2.27/0.97  
% 2.27/0.97  fof(f33,plain,(
% 2.27/0.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X6) | ~r1_tmap_1(sK3,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X6) | r1_tmap_1(sK3,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK3) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 2.27/0.97    introduced(choice_axiom,[])).
% 2.27/0.97  
% 2.27/0.97  fof(f32,plain,(
% 2.27/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6) | ~r1_tmap_1(X1,sK2,X2,X5)) & (r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6) | r1_tmap_1(X1,sK2,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.27/0.97    introduced(choice_axiom,[])).
% 2.27/0.97  
% 2.27/0.97  fof(f39,plain,(
% 2.27/0.97    (((((((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | ~r1_tmap_1(sK3,sK2,sK4,sK7)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | r1_tmap_1(sK3,sK2,sK4,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK5)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK3) & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.27/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f31,f38,f37,f36,f35,f34,f33,f32])).
% 2.27/0.97  
% 2.27/0.97  fof(f64,plain,(
% 2.27/0.97    m1_pre_topc(sK5,sK3)),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f6,axiom,(
% 2.27/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.27/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/0.97  
% 2.27/0.97  fof(f19,plain,(
% 2.27/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/0.97    inference(ennf_transformation,[],[f6])).
% 2.27/0.97  
% 2.27/0.97  fof(f20,plain,(
% 2.27/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.97    inference(flattening,[],[f19])).
% 2.27/0.97  
% 2.27/0.97  fof(f29,plain,(
% 2.27/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.97    inference(nnf_transformation,[],[f20])).
% 2.27/0.97  
% 2.27/0.97  fof(f53,plain,(
% 2.27/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/0.97    inference(cnf_transformation,[],[f29])).
% 2.27/0.97  
% 2.27/0.97  fof(f75,plain,(
% 2.27/0.97    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/0.97    inference(equality_resolution,[],[f53])).
% 2.27/0.97  
% 2.27/0.97  fof(f61,plain,(
% 2.27/0.97    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f60,plain,(
% 2.27/0.97    v1_funct_1(sK4)),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f57,plain,(
% 2.27/0.97    ~v2_struct_0(sK3)),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f58,plain,(
% 2.27/0.97    v2_pre_topc(sK3)),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f59,plain,(
% 2.27/0.97    l1_pre_topc(sK3)),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f63,plain,(
% 2.27/0.97    ~v2_struct_0(sK5)),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f56,plain,(
% 2.27/0.97    l1_pre_topc(sK2)),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f54,plain,(
% 2.27/0.97    ~v2_struct_0(sK2)),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f55,plain,(
% 2.27/0.97    v2_pre_topc(sK2)),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f62,plain,(
% 2.27/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f2,axiom,(
% 2.27/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.27/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/0.97  
% 2.27/0.97  fof(f9,plain,(
% 2.27/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.27/0.97    inference(pure_predicate_removal,[],[f2])).
% 2.27/0.97  
% 2.27/0.97  fof(f12,plain,(
% 2.27/0.97    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/0.97    inference(ennf_transformation,[],[f9])).
% 2.27/0.97  
% 2.27/0.97  fof(f13,plain,(
% 2.27/0.97    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.97    inference(flattening,[],[f12])).
% 2.27/0.97  
% 2.27/0.97  fof(f23,plain,(
% 2.27/0.97    ! [X2,X1,X0] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_connsp_2(sK0(X0,X1,X2),X0,X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.27/0.97    introduced(choice_axiom,[])).
% 2.27/0.97  
% 2.27/0.97  fof(f24,plain,(
% 2.27/0.97    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_connsp_2(sK0(X0,X1,X2),X0,X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f23])).
% 2.27/0.97  
% 2.27/0.97  fof(f44,plain,(
% 2.27/0.97    ( ! [X2,X0,X1] : (r1_tarski(sK0(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/0.97    inference(cnf_transformation,[],[f24])).
% 2.27/0.97  
% 2.27/0.97  fof(f42,plain,(
% 2.27/0.97    ( ! [X2,X0,X1] : (m1_connsp_2(sK0(X0,X1,X2),X0,X1) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/0.97    inference(cnf_transformation,[],[f24])).
% 2.27/0.97  
% 2.27/0.97  fof(f41,plain,(
% 2.27/0.97    ( ! [X2,X0,X1] : (m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/0.97    inference(cnf_transformation,[],[f24])).
% 2.27/0.97  
% 2.27/0.97  fof(f3,axiom,(
% 2.27/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 2.27/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/0.97  
% 2.27/0.97  fof(f14,plain,(
% 2.27/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/0.97    inference(ennf_transformation,[],[f3])).
% 2.27/0.97  
% 2.27/0.97  fof(f15,plain,(
% 2.27/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.97    inference(flattening,[],[f14])).
% 2.27/0.97  
% 2.27/0.97  fof(f25,plain,(
% 2.27/0.97    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.97    inference(nnf_transformation,[],[f15])).
% 2.27/0.97  
% 2.27/0.97  fof(f26,plain,(
% 2.27/0.97    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.97    inference(rectify,[],[f25])).
% 2.27/0.97  
% 2.27/0.97  fof(f27,plain,(
% 2.27/0.97    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.27/0.97    introduced(choice_axiom,[])).
% 2.27/0.97  
% 2.27/0.97  fof(f28,plain,(
% 2.27/0.97    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 2.27/0.97  
% 2.27/0.97  fof(f49,plain,(
% 2.27/0.97    ( ! [X2,X0,X3,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/0.97    inference(cnf_transformation,[],[f28])).
% 2.27/0.97  
% 2.27/0.97  fof(f1,axiom,(
% 2.27/0.97    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.27/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/0.97  
% 2.27/0.97  fof(f10,plain,(
% 2.27/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.27/0.97    inference(ennf_transformation,[],[f1])).
% 2.27/0.97  
% 2.27/0.97  fof(f11,plain,(
% 2.27/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.27/0.97    inference(flattening,[],[f10])).
% 2.27/0.97  
% 2.27/0.97  fof(f40,plain,(
% 2.27/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.27/0.97    inference(cnf_transformation,[],[f11])).
% 2.27/0.97  
% 2.27/0.97  fof(f52,plain,(
% 2.27/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/0.97    inference(cnf_transformation,[],[f29])).
% 2.27/0.97  
% 2.27/0.97  fof(f76,plain,(
% 2.27/0.97    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/0.97    inference(equality_resolution,[],[f52])).
% 2.27/0.97  
% 2.27/0.97  fof(f5,axiom,(
% 2.27/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.27/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/0.97  
% 2.27/0.97  fof(f17,plain,(
% 2.27/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/0.97    inference(ennf_transformation,[],[f5])).
% 2.27/0.97  
% 2.27/0.97  fof(f18,plain,(
% 2.27/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.97    inference(flattening,[],[f17])).
% 2.27/0.97  
% 2.27/0.97  fof(f51,plain,(
% 2.27/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/0.97    inference(cnf_transformation,[],[f18])).
% 2.27/0.97  
% 2.27/0.97  fof(f74,plain,(
% 2.27/0.97    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/0.97    inference(equality_resolution,[],[f51])).
% 2.27/0.97  
% 2.27/0.97  fof(f71,plain,(
% 2.27/0.97    sK7 = sK8),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f4,axiom,(
% 2.27/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.27/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/0.97  
% 2.27/0.97  fof(f16,plain,(
% 2.27/0.97    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.27/0.97    inference(ennf_transformation,[],[f4])).
% 2.27/0.97  
% 2.27/0.97  fof(f50,plain,(
% 2.27/0.97    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.27/0.97    inference(cnf_transformation,[],[f16])).
% 2.27/0.97  
% 2.27/0.97  fof(f73,plain,(
% 2.27/0.97    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | ~r1_tmap_1(sK3,sK2,sK4,sK7)),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f72,plain,(
% 2.27/0.97    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | r1_tmap_1(sK3,sK2,sK4,sK7)),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f70,plain,(
% 2.27/0.97    r1_tarski(sK6,u1_struct_0(sK5))),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f69,plain,(
% 2.27/0.97    r2_hidden(sK7,sK6)),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f68,plain,(
% 2.27/0.97    v3_pre_topc(sK6,sK3)),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f67,plain,(
% 2.27/0.97    m1_subset_1(sK8,u1_struct_0(sK5))),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f66,plain,(
% 2.27/0.97    m1_subset_1(sK7,u1_struct_0(sK3))),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  fof(f65,plain,(
% 2.27/0.97    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.27/0.97    inference(cnf_transformation,[],[f39])).
% 2.27/0.97  
% 2.27/0.97  cnf(c_23,negated_conjecture,
% 2.27/0.97      ( m1_pre_topc(sK5,sK3) ),
% 2.27/0.97      inference(cnf_transformation,[],[f64]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_12,plain,
% 2.27/0.97      ( r1_tmap_1(X0,X1,X2,X3)
% 2.27/0.97      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.27/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.27/0.97      | ~ m1_connsp_2(X5,X0,X3)
% 2.27/0.97      | ~ m1_pre_topc(X4,X0)
% 2.27/0.97      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.27/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.27/0.97      | ~ v1_funct_1(X2)
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | v2_struct_0(X4)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ v2_pre_topc(X0)
% 2.27/0.97      | ~ l1_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X0) ),
% 2.27/0.97      inference(cnf_transformation,[],[f75]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_26,negated_conjecture,
% 2.27/0.97      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 2.27/0.97      inference(cnf_transformation,[],[f61]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_733,plain,
% 2.27/0.97      ( r1_tmap_1(X0,X1,X2,X3)
% 2.27/0.97      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.27/0.97      | ~ m1_connsp_2(X5,X0,X3)
% 2.27/0.97      | ~ m1_pre_topc(X4,X0)
% 2.27/0.97      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.27/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.27/0.97      | ~ v1_funct_1(X2)
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | v2_struct_0(X4)
% 2.27/0.97      | ~ v2_pre_topc(X0)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X0)
% 2.27/0.97      | ~ l1_pre_topc(X1)
% 2.27/0.97      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.27/0.97      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.27/0.97      | sK4 != X2 ),
% 2.27/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_26]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_734,plain,
% 2.27/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.27/0.97      | r1_tmap_1(X2,X1,sK4,X3)
% 2.27/0.97      | ~ m1_connsp_2(X4,X2,X3)
% 2.27/0.97      | ~ m1_pre_topc(X0,X2)
% 2.27/0.97      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.27/0.97      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.27/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/0.97      | ~ v1_funct_1(sK4)
% 2.27/0.97      | v2_struct_0(X2)
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | ~ v2_pre_topc(X2)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X2)
% 2.27/0.97      | ~ l1_pre_topc(X1)
% 2.27/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.27/0.97      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.27/0.97      inference(unflattening,[status(thm)],[c_733]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_27,negated_conjecture,
% 2.27/0.97      ( v1_funct_1(sK4) ),
% 2.27/0.97      inference(cnf_transformation,[],[f60]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_738,plain,
% 2.27/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/0.97      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/0.97      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_pre_topc(X0,X2)
% 2.27/0.97      | ~ m1_connsp_2(X4,X2,X3)
% 2.27/0.97      | r1_tmap_1(X2,X1,sK4,X3)
% 2.27/0.97      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.27/0.97      | v2_struct_0(X2)
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | ~ v2_pre_topc(X2)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X2)
% 2.27/0.97      | ~ l1_pre_topc(X1)
% 2.27/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.27/0.97      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.27/0.97      inference(global_propositional_subsumption,
% 2.27/0.97                [status(thm)],
% 2.27/0.97                [c_734,c_27]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_739,plain,
% 2.27/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.27/0.97      | r1_tmap_1(X2,X1,sK4,X3)
% 2.27/0.97      | ~ m1_connsp_2(X4,X2,X3)
% 2.27/0.97      | ~ m1_pre_topc(X0,X2)
% 2.27/0.97      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.27/0.97      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.27/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | v2_struct_0(X2)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ v2_pre_topc(X2)
% 2.27/0.97      | ~ l1_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X2)
% 2.27/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.27/0.97      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.27/0.97      inference(renaming,[status(thm)],[c_738]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_864,plain,
% 2.27/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.27/0.97      | r1_tmap_1(X2,X1,sK4,X3)
% 2.27/0.97      | ~ m1_connsp_2(X4,X2,X3)
% 2.27/0.97      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.27/0.97      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.27/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | v2_struct_0(X2)
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | ~ v2_pre_topc(X2)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X2)
% 2.27/0.97      | ~ l1_pre_topc(X1)
% 2.27/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.27/0.97      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.27/0.97      | sK3 != X2
% 2.27/0.97      | sK5 != X0 ),
% 2.27/0.97      inference(resolution_lifted,[status(thm)],[c_23,c_739]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_865,plain,
% 2.27/0.97      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.27/0.97      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.27/0.97      | ~ m1_connsp_2(X2,sK3,X1)
% 2.27/0.97      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | v2_struct_0(sK3)
% 2.27/0.97      | v2_struct_0(sK5)
% 2.27/0.97      | ~ v2_pre_topc(X0)
% 2.27/0.97      | ~ v2_pre_topc(sK3)
% 2.27/0.97      | ~ l1_pre_topc(X0)
% 2.27/0.97      | ~ l1_pre_topc(sK3)
% 2.27/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.27/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.27/0.97      inference(unflattening,[status(thm)],[c_864]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_30,negated_conjecture,
% 2.27/0.97      ( ~ v2_struct_0(sK3) ),
% 2.27/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_29,negated_conjecture,
% 2.27/0.97      ( v2_pre_topc(sK3) ),
% 2.27/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_28,negated_conjecture,
% 2.27/0.97      ( l1_pre_topc(sK3) ),
% 2.27/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_24,negated_conjecture,
% 2.27/0.97      ( ~ v2_struct_0(sK5) ),
% 2.27/0.97      inference(cnf_transformation,[],[f63]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_869,plain,
% 2.27/0.97      ( ~ l1_pre_topc(X0)
% 2.27/0.97      | r1_tmap_1(sK3,X0,sK4,X1)
% 2.27/0.97      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.27/0.97      | ~ m1_connsp_2(X2,sK3,X1)
% 2.27/0.97      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | ~ v2_pre_topc(X0)
% 2.27/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.27/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.27/0.97      inference(global_propositional_subsumption,
% 2.27/0.97                [status(thm)],
% 2.27/0.97                [c_865,c_30,c_29,c_28,c_24]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_870,plain,
% 2.27/0.97      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.27/0.97      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.27/0.97      | ~ m1_connsp_2(X2,sK3,X1)
% 2.27/0.97      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | ~ v2_pre_topc(X0)
% 2.27/0.97      | ~ l1_pre_topc(X0)
% 2.27/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.27/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.27/0.97      inference(renaming,[status(thm)],[c_869]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_31,negated_conjecture,
% 2.27/0.97      ( l1_pre_topc(sK2) ),
% 2.27/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1374,plain,
% 2.27/0.97      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.27/0.97      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.27/0.97      | ~ m1_connsp_2(X2,sK3,X1)
% 2.27/0.97      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | ~ v2_pre_topc(X0)
% 2.27/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.27/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.27/0.97      | sK2 != X0 ),
% 2.27/0.97      inference(resolution_lifted,[status(thm)],[c_870,c_31]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1375,plain,
% 2.27/0.97      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.27/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.27/0.97      | ~ m1_connsp_2(X1,sK3,X0)
% 2.27/0.97      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 2.27/0.97      | v2_struct_0(sK2)
% 2.27/0.97      | ~ v2_pre_topc(sK2)
% 2.27/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.27/0.97      inference(unflattening,[status(thm)],[c_1374]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_33,negated_conjecture,
% 2.27/0.97      ( ~ v2_struct_0(sK2) ),
% 2.27/0.97      inference(cnf_transformation,[],[f54]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_32,negated_conjecture,
% 2.27/0.97      ( v2_pre_topc(sK2) ),
% 2.27/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_25,negated_conjecture,
% 2.27/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 2.27/0.97      inference(cnf_transformation,[],[f62]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1379,plain,
% 2.27/0.97      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.27/0.97      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_connsp_2(X1,sK3,X0)
% 2.27/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.27/0.97      | r1_tmap_1(sK3,sK2,sK4,X0)
% 2.27/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.27/0.97      inference(global_propositional_subsumption,
% 2.27/0.97                [status(thm)],
% 2.27/0.97                [c_1375,c_33,c_32,c_25]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1380,plain,
% 2.27/0.97      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.27/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.27/0.97      | ~ m1_connsp_2(X1,sK3,X0)
% 2.27/0.97      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.27/0.97      inference(renaming,[status(thm)],[c_1379]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_3368,plain,
% 2.27/0.97      ( r1_tmap_1(sK3,sK2,sK4,X0_53)
% 2.27/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_53)
% 2.27/0.97      | ~ m1_connsp_2(X1_53,sK3,X0_53)
% 2.27/0.97      | ~ r1_tarski(X1_53,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0_53,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.27/0.97      inference(subtyping,[status(esa)],[c_1380]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_3558,plain,
% 2.27/0.97      ( r1_tmap_1(sK3,sK2,sK4,X0_53)
% 2.27/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_53)
% 2.27/0.97      | ~ m1_connsp_2(X1_53,sK3,X0_53)
% 2.27/0.97      | ~ r1_tarski(X1_53,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0_53,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.27/0.97      inference(equality_resolution_simp,[status(thm)],[c_3368]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_5300,plain,
% 2.27/0.97      ( r1_tmap_1(sK3,sK2,sK4,X0_53)
% 2.27/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_53)
% 2.27/0.97      | ~ m1_connsp_2(sK0(sK3,sK7,u1_struct_0(sK5)),sK3,X0_53)
% 2.27/0.97      | ~ r1_tarski(sK0(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0_53,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(sK0(sK3,sK7,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_3558]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_6136,plain,
% 2.27/0.97      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.27/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.27/0.97      | ~ m1_connsp_2(sK0(sK3,sK7,u1_struct_0(sK5)),sK3,sK7)
% 2.27/0.97      | ~ r1_tarski(sK0(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(sK0(sK3,sK7,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_5300]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_3398,plain,
% 2.27/0.97      ( ~ r1_tmap_1(X0_54,X1_54,X0_53,X1_53)
% 2.27/0.97      | r1_tmap_1(X0_54,X1_54,X2_53,X3_53)
% 2.27/0.97      | X2_53 != X0_53
% 2.27/0.97      | X3_53 != X1_53 ),
% 2.27/0.97      theory(equality) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4703,plain,
% 2.27/0.97      ( r1_tmap_1(sK5,sK2,X0_53,X1_53)
% 2.27/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.27/0.97      | X0_53 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.27/0.97      | X1_53 != sK7 ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_3398]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_5388,plain,
% 2.27/0.97      ( r1_tmap_1(sK5,sK2,X0_53,sK8)
% 2.27/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.27/0.97      | X0_53 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.27/0.97      | sK8 != sK7 ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_4703]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_5803,plain,
% 2.27/0.97      ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.27/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 2.27/0.97      | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.27/0.97      | sK8 != sK7 ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_5388]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_3390,plain,
% 2.27/0.97      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 2.27/0.97      theory(equality) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4818,plain,
% 2.27/0.97      ( X0_53 != X1_53 | X0_53 = sK7 | sK7 != X1_53 ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_3390]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4970,plain,
% 2.27/0.97      ( X0_53 = sK7 | X0_53 != sK8 | sK7 != sK8 ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_4818]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_5041,plain,
% 2.27/0.97      ( sK7 != sK8 | sK8 = sK7 | sK8 != sK8 ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_4970]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.27/0.97      | r1_tarski(sK0(X1,X2,X0),X0)
% 2.27/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X1) ),
% 2.27/0.97      inference(cnf_transformation,[],[f44]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1613,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.27/0.97      | r1_tarski(sK0(X1,X2,X0),X0)
% 2.27/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | sK3 != X1 ),
% 2.27/0.97      inference(resolution_lifted,[status(thm)],[c_1,c_28]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1614,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.27/0.97      | r1_tarski(sK0(sK3,X1,X0),X0)
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | v2_struct_0(sK3)
% 2.27/0.97      | ~ v2_pre_topc(sK3) ),
% 2.27/0.97      inference(unflattening,[status(thm)],[c_1613]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1618,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.27/0.97      | r1_tarski(sK0(sK3,X1,X0),X0)
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.27/0.97      inference(global_propositional_subsumption,
% 2.27/0.97                [status(thm)],
% 2.27/0.97                [c_1614,c_30,c_29]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_3359,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0_53,sK3,X1_53)
% 2.27/0.97      | r1_tarski(sK0(sK3,X1_53,X0_53),X0_53)
% 2.27/0.97      | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.27/0.97      inference(subtyping,[status(esa)],[c_1618]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4610,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0_53,sK3,sK7)
% 2.27/0.97      | r1_tarski(sK0(sK3,sK7,X0_53),X0_53)
% 2.27/0.97      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_3359]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_5007,plain,
% 2.27/0.97      ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
% 2.27/0.97      | r1_tarski(sK0(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_4610]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_3,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.27/0.97      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 2.27/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X1) ),
% 2.27/0.97      inference(cnf_transformation,[],[f42]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1565,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.27/0.97      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 2.27/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | sK3 != X1 ),
% 2.27/0.97      inference(resolution_lifted,[status(thm)],[c_3,c_28]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1566,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.27/0.97      | m1_connsp_2(sK0(sK3,X1,X0),sK3,X1)
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | v2_struct_0(sK3)
% 2.27/0.97      | ~ v2_pre_topc(sK3) ),
% 2.27/0.97      inference(unflattening,[status(thm)],[c_1565]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1570,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.27/0.97      | m1_connsp_2(sK0(sK3,X1,X0),sK3,X1)
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.27/0.97      inference(global_propositional_subsumption,
% 2.27/0.97                [status(thm)],
% 2.27/0.97                [c_1566,c_30,c_29]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_3361,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0_53,sK3,X1_53)
% 2.27/0.97      | m1_connsp_2(sK0(sK3,X1_53,X0_53),sK3,X1_53)
% 2.27/0.97      | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.27/0.97      inference(subtyping,[status(esa)],[c_1570]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4615,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0_53,sK3,sK7)
% 2.27/0.97      | m1_connsp_2(sK0(sK3,sK7,X0_53),sK3,sK7)
% 2.27/0.97      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_3361]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_5009,plain,
% 2.27/0.97      ( m1_connsp_2(sK0(sK3,sK7,u1_struct_0(sK5)),sK3,sK7)
% 2.27/0.97      | ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
% 2.27/0.97      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_4615]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.27/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/0.97      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X1) ),
% 2.27/0.97      inference(cnf_transformation,[],[f41]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1541,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.27/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/0.97      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | sK3 != X1 ),
% 2.27/0.97      inference(resolution_lifted,[status(thm)],[c_4,c_28]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1542,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | m1_subset_1(sK0(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | v2_struct_0(sK3)
% 2.27/0.97      | ~ v2_pre_topc(sK3) ),
% 2.27/0.97      inference(unflattening,[status(thm)],[c_1541]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1546,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | m1_subset_1(sK0(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.27/0.97      inference(global_propositional_subsumption,
% 2.27/0.97                [status(thm)],
% 2.27/0.97                [c_1542,c_30,c_29]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_3362,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0_53,sK3,X1_53)
% 2.27/0.97      | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | m1_subset_1(sK0(sK3,X1_53,X0_53),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.27/0.97      inference(subtyping,[status(esa)],[c_1546]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4591,plain,
% 2.27/0.97      ( ~ m1_connsp_2(X0_53,sK3,sK7)
% 2.27/0.97      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | m1_subset_1(sK0(sK3,sK7,X0_53),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_3362]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_5012,plain,
% 2.27/0.97      ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
% 2.27/0.97      | m1_subset_1(sK0(sK3,sK7,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_4591]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_5,plain,
% 2.27/0.97      ( m1_connsp_2(X0,X1,X2)
% 2.27/0.97      | ~ v3_pre_topc(X3,X1)
% 2.27/0.97      | ~ r1_tarski(X3,X0)
% 2.27/0.97      | ~ r2_hidden(X2,X3)
% 2.27/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X1) ),
% 2.27/0.97      inference(cnf_transformation,[],[f49]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1506,plain,
% 2.27/0.97      ( m1_connsp_2(X0,X1,X2)
% 2.27/0.97      | ~ v3_pre_topc(X3,X1)
% 2.27/0.97      | ~ r1_tarski(X3,X0)
% 2.27/0.97      | ~ r2_hidden(X2,X3)
% 2.27/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | sK3 != X1 ),
% 2.27/0.97      inference(resolution_lifted,[status(thm)],[c_5,c_28]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1507,plain,
% 2.27/0.97      ( m1_connsp_2(X0,sK3,X1)
% 2.27/0.97      | ~ v3_pre_topc(X2,sK3)
% 2.27/0.97      | ~ r1_tarski(X2,X0)
% 2.27/0.97      | ~ r2_hidden(X1,X2)
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | v2_struct_0(sK3)
% 2.27/0.97      | ~ v2_pre_topc(sK3) ),
% 2.27/0.97      inference(unflattening,[status(thm)],[c_1506]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1511,plain,
% 2.27/0.97      ( m1_connsp_2(X0,sK3,X1)
% 2.27/0.97      | ~ v3_pre_topc(X2,sK3)
% 2.27/0.97      | ~ r1_tarski(X2,X0)
% 2.27/0.97      | ~ r2_hidden(X1,X2)
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.27/0.97      inference(global_propositional_subsumption,
% 2.27/0.97                [status(thm)],
% 2.27/0.97                [c_1507,c_30,c_29]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_0,plain,
% 2.27/0.97      ( ~ r2_hidden(X0,X1)
% 2.27/0.97      | m1_subset_1(X0,X2)
% 2.27/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.27/0.97      inference(cnf_transformation,[],[f40]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1531,plain,
% 2.27/0.97      ( m1_connsp_2(X0,sK3,X1)
% 2.27/0.97      | ~ v3_pre_topc(X2,sK3)
% 2.27/0.97      | ~ r1_tarski(X2,X0)
% 2.27/0.97      | ~ r2_hidden(X1,X2)
% 2.27/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.27/0.97      inference(forward_subsumption_resolution,
% 2.27/0.97                [status(thm)],
% 2.27/0.97                [c_1511,c_0]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_3363,plain,
% 2.27/0.97      ( m1_connsp_2(X0_53,sK3,X1_53)
% 2.27/0.97      | ~ v3_pre_topc(X2_53,sK3)
% 2.27/0.97      | ~ r1_tarski(X2_53,X0_53)
% 2.27/0.97      | ~ r2_hidden(X1_53,X2_53)
% 2.27/0.97      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(X2_53,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.27/0.97      inference(subtyping,[status(esa)],[c_1531]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4642,plain,
% 2.27/0.97      ( m1_connsp_2(X0_53,sK3,X1_53)
% 2.27/0.97      | ~ v3_pre_topc(sK6,sK3)
% 2.27/0.97      | ~ r1_tarski(sK6,X0_53)
% 2.27/0.97      | ~ r2_hidden(X1_53,sK6)
% 2.27/0.97      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_3363]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4881,plain,
% 2.27/0.97      ( m1_connsp_2(u1_struct_0(sK5),sK3,X0_53)
% 2.27/0.97      | ~ v3_pre_topc(sK6,sK3)
% 2.27/0.97      | ~ r1_tarski(sK6,u1_struct_0(sK5))
% 2.27/0.97      | ~ r2_hidden(X0_53,sK6)
% 2.27/0.97      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_4642]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_5005,plain,
% 2.27/0.97      ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
% 2.27/0.97      | ~ v3_pre_topc(sK6,sK3)
% 2.27/0.97      | ~ r1_tarski(sK6,u1_struct_0(sK5))
% 2.27/0.97      | ~ r2_hidden(sK7,sK6)
% 2.27/0.97      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_4881]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_3389,plain,( X0_53 = X0_53 ),theory(equality) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4872,plain,
% 2.27/0.97      ( k2_tmap_1(sK3,sK2,sK4,sK5) = k2_tmap_1(sK3,sK2,sK4,sK5) ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_3389]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4698,plain,
% 2.27/0.97      ( r1_tmap_1(sK5,sK2,X0_53,X1_53)
% 2.27/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 2.27/0.97      | X0_53 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.27/0.97      | X1_53 != sK8 ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_3398]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4839,plain,
% 2.27/0.97      ( r1_tmap_1(sK5,sK2,X0_53,sK7)
% 2.27/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 2.27/0.97      | X0_53 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.27/0.97      | sK7 != sK8 ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_4698]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4871,plain,
% 2.27/0.97      ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.27/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 2.27/0.97      | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.27/0.97      | sK7 != sK8 ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_4839]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4866,plain,
% 2.27/0.97      ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_3389]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_3391,plain,
% 2.27/0.97      ( ~ m1_subset_1(X0_53,X1_53)
% 2.27/0.97      | m1_subset_1(X2_53,X3_53)
% 2.27/0.97      | X2_53 != X0_53
% 2.27/0.97      | X3_53 != X1_53 ),
% 2.27/0.97      theory(equality) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4663,plain,
% 2.27/0.97      ( m1_subset_1(X0_53,X1_53)
% 2.27/0.97      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.27/0.97      | X1_53 != u1_struct_0(sK5)
% 2.27/0.97      | X0_53 != sK8 ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_3391]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4791,plain,
% 2.27/0.97      ( m1_subset_1(sK7,X0_53)
% 2.27/0.97      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.27/0.97      | X0_53 != u1_struct_0(sK5)
% 2.27/0.97      | sK7 != sK8 ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_4663]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4865,plain,
% 2.27/0.97      ( m1_subset_1(sK7,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.27/0.97      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 2.27/0.97      | sK7 != sK8 ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_4791]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4797,plain,
% 2.27/0.97      ( sK8 = sK8 ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_3389]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_13,plain,
% 2.27/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.27/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.27/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.27/0.97      | ~ m1_connsp_2(X5,X0,X3)
% 2.27/0.97      | ~ m1_pre_topc(X4,X0)
% 2.27/0.97      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.27/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.27/0.97      | ~ v1_funct_1(X2)
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | v2_struct_0(X4)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ v2_pre_topc(X0)
% 2.27/0.97      | ~ l1_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X0) ),
% 2.27/0.97      inference(cnf_transformation,[],[f76]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_11,plain,
% 2.27/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.27/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.27/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.27/0.97      | ~ m1_pre_topc(X4,X0)
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.27/0.97      | ~ v1_funct_1(X2)
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | v2_struct_0(X4)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ v2_pre_topc(X0)
% 2.27/0.97      | ~ l1_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X0) ),
% 2.27/0.97      inference(cnf_transformation,[],[f74]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_181,plain,
% 2.27/0.97      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.27/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.27/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.27/0.97      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.27/0.97      | ~ m1_pre_topc(X4,X0)
% 2.27/0.97      | ~ v1_funct_1(X2)
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | v2_struct_0(X4)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ v2_pre_topc(X0)
% 2.27/0.97      | ~ l1_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X0) ),
% 2.27/0.97      inference(global_propositional_subsumption,
% 2.27/0.97                [status(thm)],
% 2.27/0.97                [c_13,c_11]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_182,plain,
% 2.27/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.27/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.27/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.27/0.97      | ~ m1_pre_topc(X4,X0)
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.27/0.97      | ~ v1_funct_1(X2)
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | v2_struct_0(X4)
% 2.27/0.97      | ~ v2_pre_topc(X0)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X0)
% 2.27/0.97      | ~ l1_pre_topc(X1) ),
% 2.27/0.97      inference(renaming,[status(thm)],[c_181]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_676,plain,
% 2.27/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.27/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.27/0.97      | ~ m1_pre_topc(X4,X0)
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.27/0.97      | ~ v1_funct_1(X2)
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | v2_struct_0(X4)
% 2.27/0.97      | ~ v2_pre_topc(X0)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X0)
% 2.27/0.97      | ~ l1_pre_topc(X1)
% 2.27/0.97      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.27/0.97      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.27/0.97      | sK4 != X2 ),
% 2.27/0.97      inference(resolution_lifted,[status(thm)],[c_182,c_26]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_677,plain,
% 2.27/0.97      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.27/0.97      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.27/0.97      | ~ m1_pre_topc(X0,X2)
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.27/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/0.97      | ~ v1_funct_1(sK4)
% 2.27/0.97      | v2_struct_0(X2)
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | ~ v2_pre_topc(X2)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X2)
% 2.27/0.97      | ~ l1_pre_topc(X1)
% 2.27/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.27/0.97      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.27/0.97      inference(unflattening,[status(thm)],[c_676]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_681,plain,
% 2.27/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_pre_topc(X0,X2)
% 2.27/0.97      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.27/0.97      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.27/0.97      | v2_struct_0(X2)
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | ~ v2_pre_topc(X2)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X2)
% 2.27/0.97      | ~ l1_pre_topc(X1)
% 2.27/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.27/0.97      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.27/0.97      inference(global_propositional_subsumption,
% 2.27/0.97                [status(thm)],
% 2.27/0.97                [c_677,c_27]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_682,plain,
% 2.27/0.97      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.27/0.97      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.27/0.97      | ~ m1_pre_topc(X0,X2)
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.27/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | v2_struct_0(X2)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ v2_pre_topc(X2)
% 2.27/0.97      | ~ l1_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X2)
% 2.27/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.27/0.97      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.27/0.97      inference(renaming,[status(thm)],[c_681]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_915,plain,
% 2.27/0.97      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.27/0.97      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.27/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | v2_struct_0(X2)
% 2.27/0.97      | v2_struct_0(X1)
% 2.27/0.97      | ~ v2_pre_topc(X2)
% 2.27/0.97      | ~ v2_pre_topc(X1)
% 2.27/0.97      | ~ l1_pre_topc(X2)
% 2.27/0.97      | ~ l1_pre_topc(X1)
% 2.27/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.27/0.97      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.27/0.97      | sK3 != X2
% 2.27/0.97      | sK5 != X0 ),
% 2.27/0.97      inference(resolution_lifted,[status(thm)],[c_23,c_682]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_916,plain,
% 2.27/0.97      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.27/0.97      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | v2_struct_0(sK3)
% 2.27/0.97      | v2_struct_0(sK5)
% 2.27/0.97      | ~ v2_pre_topc(X0)
% 2.27/0.97      | ~ v2_pre_topc(sK3)
% 2.27/0.97      | ~ l1_pre_topc(X0)
% 2.27/0.97      | ~ l1_pre_topc(sK3)
% 2.27/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.27/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.27/0.97      inference(unflattening,[status(thm)],[c_915]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_920,plain,
% 2.27/0.97      ( ~ l1_pre_topc(X0)
% 2.27/0.97      | ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.27/0.97      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | ~ v2_pre_topc(X0)
% 2.27/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.27/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.27/0.97      inference(global_propositional_subsumption,
% 2.27/0.97                [status(thm)],
% 2.27/0.97                [c_916,c_30,c_29,c_28,c_24]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_921,plain,
% 2.27/0.97      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.27/0.97      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | ~ v2_pre_topc(X0)
% 2.27/0.97      | ~ l1_pre_topc(X0)
% 2.27/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.27/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.27/0.97      inference(renaming,[status(thm)],[c_920]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1347,plain,
% 2.27/0.97      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.27/0.97      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.27/0.97      | v2_struct_0(X0)
% 2.27/0.97      | ~ v2_pre_topc(X0)
% 2.27/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.27/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.27/0.97      | sK2 != X0 ),
% 2.27/0.97      inference(resolution_lifted,[status(thm)],[c_921,c_31]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1348,plain,
% 2.27/0.97      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.27/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.27/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 2.27/0.97      | v2_struct_0(sK2)
% 2.27/0.97      | ~ v2_pre_topc(sK2)
% 2.27/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.27/0.97      inference(unflattening,[status(thm)],[c_1347]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1352,plain,
% 2.27/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.27/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.27/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.27/0.97      | ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.27/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.27/0.97      inference(global_propositional_subsumption,
% 2.27/0.97                [status(thm)],
% 2.27/0.97                [c_1348,c_33,c_32,c_25]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_1353,plain,
% 2.27/0.97      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.27/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.27/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.27/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.27/0.97      inference(renaming,[status(thm)],[c_1352]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_3369,plain,
% 2.27/0.97      ( ~ r1_tmap_1(sK3,sK2,sK4,X0_53)
% 2.27/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_53)
% 2.27/0.97      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0_53,u1_struct_0(sK5))
% 2.27/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.27/0.97      inference(subtyping,[status(esa)],[c_1353]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_3554,plain,
% 2.27/0.97      ( ~ r1_tmap_1(sK3,sK2,sK4,X0_53)
% 2.27/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_53)
% 2.27/0.97      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(X0_53,u1_struct_0(sK5)) ),
% 2.27/0.97      inference(equality_resolution_simp,[status(thm)],[c_3369]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_4634,plain,
% 2.27/0.97      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.27/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.27/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.27/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 2.27/0.97      inference(instantiation,[status(thm)],[c_3554]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_16,negated_conjecture,
% 2.27/0.97      ( sK7 = sK8 ),
% 2.27/0.97      inference(cnf_transformation,[],[f71]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_3380,negated_conjecture,
% 2.27/0.97      ( sK7 = sK8 ),
% 2.27/0.97      inference(subtyping,[status(esa)],[c_16]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_10,plain,
% 2.27/0.97      ( ~ m1_pre_topc(X0,X1)
% 2.27/0.97      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/0.97      | ~ l1_pre_topc(X1) ),
% 2.27/0.97      inference(cnf_transformation,[],[f50]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_853,plain,
% 2.27/0.97      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/0.97      | ~ l1_pre_topc(X1)
% 2.27/0.97      | sK3 != X1
% 2.27/0.97      | sK5 != X0 ),
% 2.27/0.97      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_854,plain,
% 2.27/0.97      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.27/0.97      | ~ l1_pre_topc(sK3) ),
% 2.27/0.97      inference(unflattening,[status(thm)],[c_853]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_14,negated_conjecture,
% 2.27/0.97      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.27/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 2.27/0.97      inference(cnf_transformation,[],[f73]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_15,negated_conjecture,
% 2.27/0.97      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.27/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 2.27/0.97      inference(cnf_transformation,[],[f72]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_17,negated_conjecture,
% 2.27/0.97      ( r1_tarski(sK6,u1_struct_0(sK5)) ),
% 2.27/0.97      inference(cnf_transformation,[],[f70]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_18,negated_conjecture,
% 2.27/0.97      ( r2_hidden(sK7,sK6) ),
% 2.27/0.97      inference(cnf_transformation,[],[f69]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_19,negated_conjecture,
% 2.27/0.97      ( v3_pre_topc(sK6,sK3) ),
% 2.27/0.97      inference(cnf_transformation,[],[f68]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_20,negated_conjecture,
% 2.27/0.97      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 2.27/0.97      inference(cnf_transformation,[],[f67]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_21,negated_conjecture,
% 2.27/0.97      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.27/0.97      inference(cnf_transformation,[],[f66]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(c_22,negated_conjecture,
% 2.27/0.97      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.27/0.97      inference(cnf_transformation,[],[f65]) ).
% 2.27/0.97  
% 2.27/0.97  cnf(contradiction,plain,
% 2.27/0.97      ( $false ),
% 2.27/0.97      inference(minisat,
% 2.27/0.97                [status(thm)],
% 2.27/0.97                [c_6136,c_5803,c_5041,c_5007,c_5009,c_5012,c_5005,c_4872,
% 2.27/0.97                 c_4871,c_4866,c_4865,c_4797,c_4634,c_3380,c_854,c_14,
% 2.27/0.97                 c_15,c_17,c_18,c_19,c_20,c_21,c_22,c_28]) ).
% 2.27/0.97  
% 2.27/0.97  
% 2.27/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.27/0.97  
% 2.27/0.97  ------                               Statistics
% 2.27/0.97  
% 2.27/0.97  ------ General
% 2.27/0.97  
% 2.27/0.97  abstr_ref_over_cycles:                  0
% 2.27/0.97  abstr_ref_under_cycles:                 0
% 2.27/0.97  gc_basic_clause_elim:                   0
% 2.27/0.97  forced_gc_time:                         0
% 2.27/0.97  parsing_time:                           0.011
% 2.27/0.97  unif_index_cands_time:                  0.
% 2.27/0.97  unif_index_add_time:                    0.
% 2.27/0.97  orderings_time:                         0.
% 2.27/0.97  out_proof_time:                         0.012
% 2.27/0.97  total_time:                             0.189
% 2.27/0.97  num_of_symbols:                         60
% 2.27/0.97  num_of_terms:                           4291
% 2.27/0.97  
% 2.27/0.97  ------ Preprocessing
% 2.27/0.97  
% 2.27/0.97  num_of_splits:                          2
% 2.27/0.97  num_of_split_atoms:                     2
% 2.27/0.97  num_of_reused_defs:                     0
% 2.27/0.97  num_eq_ax_congr_red:                    23
% 2.27/0.97  num_of_sem_filtered_clauses:            1
% 2.27/0.97  num_of_subtypes:                        2
% 2.27/0.97  monotx_restored_types:                  0
% 2.27/0.97  sat_num_of_epr_types:                   0
% 2.27/0.97  sat_num_of_non_cyclic_types:            0
% 2.27/0.97  sat_guarded_non_collapsed_types:        0
% 2.27/0.97  num_pure_diseq_elim:                    0
% 2.27/0.97  simp_replaced_by:                       0
% 2.27/0.97  res_preprocessed:                       129
% 2.27/0.97  prep_upred:                             0
% 2.27/0.97  prep_unflattend:                        122
% 2.27/0.97  smt_new_axioms:                         0
% 2.27/0.97  pred_elim_cands:                        12
% 2.27/0.97  pred_elim:                              6
% 2.27/0.97  pred_elim_cl:                           0
% 2.27/0.97  pred_elim_cycles:                       12
% 2.27/0.97  merged_defs:                            6
% 2.27/0.97  merged_defs_ncl:                        0
% 2.27/0.97  bin_hyper_res:                          6
% 2.27/0.97  prep_cycles:                            3
% 2.27/0.97  pred_elim_time:                         0.077
% 2.27/0.97  splitting_time:                         0.
% 2.27/0.97  sem_filter_time:                        0.
% 2.27/0.97  monotx_time:                            0.
% 2.27/0.97  subtype_inf_time:                       0.
% 2.27/0.97  
% 2.27/0.97  ------ Problem properties
% 2.27/0.97  
% 2.27/0.97  clauses:                                36
% 2.27/0.97  conjectures:                            10
% 2.27/0.97  epr:                                    3
% 2.27/0.97  horn:                                   35
% 2.27/0.97  ground:                                 13
% 2.27/0.97  unary:                                  9
% 2.27/0.97  binary:                                 2
% 2.27/0.97  lits:                                   124
% 2.27/0.97  lits_eq:                                5
% 2.27/0.97  fd_pure:                                0
% 2.27/0.97  fd_pseudo:                              0
% 2.27/0.97  fd_cond:                                0
% 2.27/0.97  fd_pseudo_cond:                         0
% 2.27/0.97  ac_symbols:                             0
% 2.27/0.97  
% 2.27/0.97  ------ Propositional Solver
% 2.27/0.97  
% 2.27/0.97  prop_solver_calls:                      22
% 2.27/0.97  prop_fast_solver_calls:                 2084
% 2.27/0.97  smt_solver_calls:                       0
% 2.27/0.97  smt_fast_solver_calls:                  0
% 2.27/0.97  prop_num_of_clauses:                    1399
% 2.27/0.97  prop_preprocess_simplified:             4729
% 2.27/0.97  prop_fo_subsumed:                       99
% 2.27/0.97  prop_solver_time:                       0.
% 2.27/0.97  smt_solver_time:                        0.
% 2.27/0.97  smt_fast_solver_time:                   0.
% 2.27/0.97  prop_fast_solver_time:                  0.
% 2.27/0.97  prop_unsat_core_time:                   0.
% 2.27/0.97  
% 2.27/0.97  ------ QBF
% 2.27/0.97  
% 2.27/0.97  qbf_q_res:                              0
% 2.27/0.97  qbf_num_tautologies:                    0
% 2.27/0.97  qbf_prep_cycles:                        0
% 2.27/0.97  
% 2.27/0.97  ------ BMC1
% 2.27/0.97  
% 2.27/0.97  bmc1_current_bound:                     -1
% 2.27/0.97  bmc1_last_solved_bound:                 -1
% 2.27/0.97  bmc1_unsat_core_size:                   -1
% 2.27/0.97  bmc1_unsat_core_parents_size:           -1
% 2.27/0.97  bmc1_merge_next_fun:                    0
% 2.27/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.27/0.97  
% 2.27/0.97  ------ Instantiation
% 2.27/0.97  
% 2.27/0.97  inst_num_of_clauses:                    266
% 2.27/0.97  inst_num_in_passive:                    10
% 2.27/0.97  inst_num_in_active:                     200
% 2.27/0.97  inst_num_in_unprocessed:                55
% 2.27/0.97  inst_num_of_loops:                      213
% 2.27/0.97  inst_num_of_learning_restarts:          0
% 2.27/0.97  inst_num_moves_active_passive:          9
% 2.27/0.97  inst_lit_activity:                      0
% 2.27/0.97  inst_lit_activity_moves:                0
% 2.27/0.97  inst_num_tautologies:                   0
% 2.27/0.97  inst_num_prop_implied:                  0
% 2.27/0.97  inst_num_existing_simplified:           0
% 2.27/0.97  inst_num_eq_res_simplified:             0
% 2.27/0.97  inst_num_child_elim:                    0
% 2.27/0.97  inst_num_of_dismatching_blockings:      13
% 2.27/0.97  inst_num_of_non_proper_insts:           193
% 2.27/0.97  inst_num_of_duplicates:                 0
% 2.27/0.97  inst_inst_num_from_inst_to_res:         0
% 2.27/0.97  inst_dismatching_checking_time:         0.
% 2.27/0.97  
% 2.27/0.97  ------ Resolution
% 2.27/0.97  
% 2.27/0.97  res_num_of_clauses:                     0
% 2.27/0.97  res_num_in_passive:                     0
% 2.27/0.97  res_num_in_active:                      0
% 2.27/0.97  res_num_of_loops:                       132
% 2.27/0.97  res_forward_subset_subsumed:            40
% 2.27/0.97  res_backward_subset_subsumed:           0
% 2.27/0.97  res_forward_subsumed:                   0
% 2.27/0.97  res_backward_subsumed:                  0
% 2.27/0.97  res_forward_subsumption_resolution:     7
% 2.27/0.97  res_backward_subsumption_resolution:    0
% 2.27/0.97  res_clause_to_clause_subsumption:       257
% 2.27/0.97  res_orphan_elimination:                 0
% 2.27/0.97  res_tautology_del:                      41
% 2.27/0.97  res_num_eq_res_simplified:              2
% 2.27/0.97  res_num_sel_changes:                    0
% 2.27/0.97  res_moves_from_active_to_pass:          0
% 2.27/0.97  
% 2.27/0.97  ------ Superposition
% 2.27/0.97  
% 2.27/0.97  sup_time_total:                         0.
% 2.27/0.97  sup_time_generating:                    0.
% 2.27/0.97  sup_time_sim_full:                      0.
% 2.27/0.97  sup_time_sim_immed:                     0.
% 2.27/0.97  
% 2.27/0.97  sup_num_of_clauses:                     59
% 2.27/0.97  sup_num_in_active:                      42
% 2.27/0.97  sup_num_in_passive:                     17
% 2.27/0.97  sup_num_of_loops:                       42
% 2.27/0.97  sup_fw_superposition:                   10
% 2.27/0.97  sup_bw_superposition:                   13
% 2.27/0.97  sup_immediate_simplified:               0
% 2.27/0.97  sup_given_eliminated:                   0
% 2.27/0.97  comparisons_done:                       0
% 2.27/0.97  comparisons_avoided:                    0
% 2.27/0.97  
% 2.27/0.97  ------ Simplifications
% 2.27/0.97  
% 2.27/0.97  
% 2.27/0.97  sim_fw_subset_subsumed:                 0
% 2.27/0.97  sim_bw_subset_subsumed:                 0
% 2.27/0.97  sim_fw_subsumed:                        0
% 2.27/0.97  sim_bw_subsumed:                        0
% 2.27/0.97  sim_fw_subsumption_res:                 0
% 2.27/0.97  sim_bw_subsumption_res:                 0
% 2.27/0.97  sim_tautology_del:                      1
% 2.27/0.97  sim_eq_tautology_del:                   0
% 2.27/0.97  sim_eq_res_simp:                        2
% 2.27/0.97  sim_fw_demodulated:                     0
% 2.27/0.97  sim_bw_demodulated:                     0
% 2.27/0.97  sim_light_normalised:                   4
% 2.27/0.97  sim_joinable_taut:                      0
% 2.27/0.97  sim_joinable_simp:                      0
% 2.27/0.97  sim_ac_normalised:                      0
% 2.27/0.97  sim_smt_subsumption:                    0
% 2.27/0.97  
%------------------------------------------------------------------------------
