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

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 652 expanded)
%              Number of clauses        :   91 ( 108 expanded)
%              Number of leaves         :   17 ( 287 expanded)
%              Depth                    :   25
%              Number of atoms          : 1206 (12764 expanded)
%              Number of equality atoms :   95 ( 796 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f22,plain,(
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
    inference(flattening,[],[f22])).

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,(
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

fof(f27,plain,(
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

fof(f26,plain,(
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

fof(f25,plain,(
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

fof(f24,plain,
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

fof(f31,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f23,f30,f29,f28,f27,f26,f25,f24])).

fof(f49,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f21,plain,(
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

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
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
    inference(equality_resolution,[],[f41])).

fof(f52,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f42,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
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
    inference(equality_resolution,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
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

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).

fof(f39,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | ~ r1_tmap_1(sK3,sK2,sK4,sK7) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | r1_tmap_1(sK3,sK2,sK4,sK7) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    v3_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6529,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,X0_54,X1_54)
    | r1_tmap_1(X0_53,X1_53,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_8276,plain,
    ( r1_tmap_1(sK5,sK2,X0_54,X1_54)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | X1_54 != sK7 ),
    inference(instantiation,[status(thm)],[c_6529])).

cnf(c_8756,plain,
    ( r1_tmap_1(sK5,sK2,X0_54,sK8)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK8 != sK7 ),
    inference(instantiation,[status(thm)],[c_8276])).

cnf(c_9083,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK8 != sK7 ),
    inference(instantiation,[status(thm)],[c_8756])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

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
    inference(cnf_transformation,[],[f62])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_492,plain,
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
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_493,plain,
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
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_497,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_26,c_25,c_24,c_20])).

cnf(c_498,plain,
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
    inference(renaming,[status(thm)],[c_497])).

cnf(c_545,plain,
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
    inference(resolution_lifted,[status(thm)],[c_22,c_498])).

cnf(c_546,plain,
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
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_550,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_546,c_23])).

cnf(c_551,plain,
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
    inference(renaming,[status(thm)],[c_550])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1047,plain,
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
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_551,c_27])).

cnf(c_1048,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1047])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1052,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1048,c_29,c_28,c_21])).

cnf(c_1053,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1052])).

cnf(c_3943,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_tarski(X1,u1_struct_0(sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1053])).

cnf(c_6491,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_54)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
    | ~ m1_connsp_2(X1_54,sK3,X0_54)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ r1_tarski(X1_54,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_3943])).

cnf(c_7542,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_connsp_2(X0_54,sK3,sK7)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ r1_tarski(X0_54,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6491])).

cnf(c_8410,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_connsp_2(sK6,sK3,sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_7542])).

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
    inference(cnf_transformation,[],[f63])).

cnf(c_441,plain,
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
    | sK3 != X0
    | sK5 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_442,plain,
    ( ~ r1_tmap_1(sK3,X0,X1,X2)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
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
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_446,plain,
    ( ~ l1_pre_topc(X0)
    | ~ r1_tmap_1(sK3,X0,X1,X2)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
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
    inference(global_propositional_subsumption,[status(thm)],[c_442,c_26,c_25,c_24,c_20])).

cnf(c_447,plain,
    ( ~ r1_tmap_1(sK3,X0,X1,X2)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
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
    inference(renaming,[status(thm)],[c_446])).

cnf(c_593,plain,
    ( ~ r1_tmap_1(sK3,X0,X1,X2)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
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
    inference(resolution_lifted,[status(thm)],[c_22,c_447])).

cnf(c_594,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
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
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_598,plain,
    ( ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_connsp_2(X2,sK3,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tmap_1(sK3,X0,sK4,X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_594,c_23])).

cnf(c_599,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
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
    inference(renaming,[status(thm)],[c_598])).

cnf(c_1011,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_599,c_27])).

cnf(c_1012,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1011])).

cnf(c_1016,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_connsp_2(X1,sK3,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1012,c_29,c_28,c_21])).

cnf(c_1017,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1016])).

cnf(c_3947,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_tarski(X1,u1_struct_0(sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1017])).

cnf(c_6490,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0_54)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
    | ~ m1_connsp_2(X1_54,sK3,X0_54)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ r1_tarski(X1_54,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_3947])).

cnf(c_7537,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_connsp_2(X0_54,sK3,sK7)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ r1_tarski(X0_54,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6490])).

cnf(c_8083,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_connsp_2(sK6,sK3,sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_7537])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_6515,plain,
    ( r2_hidden(sK0(X0_54,X1_54),X0_54)
    | r1_tarski(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_7679,plain,
    ( r2_hidden(sK0(sK6,X0_54),sK6)
    | r1_tarski(sK6,X0_54) ),
    inference(instantiation,[status(thm)],[c_6515])).

cnf(c_7933,plain,
    ( r2_hidden(sK0(sK6,sK6),sK6)
    | r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_7679])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6516,plain,
    ( ~ r2_hidden(sK0(X0_54,X1_54),X1_54)
    | r1_tarski(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_7678,plain,
    ( ~ r2_hidden(sK0(sK6,X0_54),X0_54)
    | r1_tarski(sK6,X0_54) ),
    inference(instantiation,[status(thm)],[c_6516])).

cnf(c_7932,plain,
    ( ~ r2_hidden(sK0(sK6,sK6),sK6)
    | r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_7678])).

cnf(c_6523,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_7644,plain,
    ( X0_54 != X1_54
    | X0_54 = sK7
    | sK7 != X1_54 ),
    inference(instantiation,[status(thm)],[c_6523])).

cnf(c_7809,plain,
    ( X0_54 = sK7
    | X0_54 != sK8
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_7644])).

cnf(c_7865,plain,
    ( sK7 != sK8
    | sK8 = sK7
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_7809])).

cnf(c_3,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1179,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_1180,plain,
    ( m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v3_pre_topc(X2,sK3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1179])).

cnf(c_1184,plain,
    ( m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v3_pre_topc(X2,sK3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1180,c_26,c_25])).

cnf(c_6497,plain,
    ( m1_connsp_2(X0_54,sK3,X1_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | ~ v3_pre_topc(X2_54,sK3)
    | ~ r2_hidden(X1_54,X2_54)
    | ~ r1_tarski(X2_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_1184])).

cnf(c_7532,plain,
    ( m1_connsp_2(X0_54,sK3,X1_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(sK6,sK3)
    | ~ r2_hidden(X1_54,sK6)
    | ~ r1_tarski(sK6,X0_54) ),
    inference(instantiation,[status(thm)],[c_6497])).

cnf(c_7670,plain,
    ( m1_connsp_2(X0_54,sK3,sK7)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ v3_pre_topc(sK6,sK3)
    | ~ r2_hidden(sK7,sK6)
    | ~ r1_tarski(sK6,X0_54) ),
    inference(instantiation,[status(thm)],[c_7532])).

cnf(c_7751,plain,
    ( m1_connsp_2(sK6,sK3,sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ v3_pre_topc(sK6,sK3)
    | ~ r2_hidden(sK7,sK6)
    | ~ r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_7670])).

cnf(c_6522,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_7719,plain,
    ( k2_tmap_1(sK3,sK2,sK4,sK5) = k2_tmap_1(sK3,sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_6522])).

cnf(c_7588,plain,
    ( r1_tmap_1(sK5,sK2,X0_54,X1_54)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | X1_54 != sK8 ),
    inference(instantiation,[status(thm)],[c_6529])).

cnf(c_7662,plain,
    ( r1_tmap_1(sK5,sK2,X0_54,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_7588])).

cnf(c_7718,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_7662])).

cnf(c_7713,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_6522])).

cnf(c_6528,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | m1_subset_1(X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_7568,plain,
    ( m1_subset_1(X0_54,X1_54)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | X1_54 != u1_struct_0(sK5)
    | X0_54 != sK8 ),
    inference(instantiation,[status(thm)],[c_6528])).

cnf(c_7615,plain,
    ( m1_subset_1(sK7,X0_54)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | X0_54 != u1_struct_0(sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_7568])).

cnf(c_7712,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_7615])).

cnf(c_7621,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_6522])).

cnf(c_12,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_6511,negated_conjecture,
    ( sK7 = sK8 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_11,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_15,negated_conjecture,
    ( v3_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9083,c_8410,c_8083,c_7933,c_7932,c_7865,c_7751,c_7719,c_7718,c_7713,c_7712,c_7621,c_6511,c_10,c_11,c_13,c_14,c_15,c_16,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:59:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.34/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/0.98  
% 2.34/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.34/0.98  
% 2.34/0.98  ------  iProver source info
% 2.34/0.98  
% 2.34/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.34/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.34/0.98  git: non_committed_changes: false
% 2.34/0.98  git: last_make_outside_of_git: false
% 2.34/0.98  
% 2.34/0.98  ------ 
% 2.34/0.98  
% 2.34/0.98  ------ Input Options
% 2.34/0.98  
% 2.34/0.98  --out_options                           all
% 2.34/0.98  --tptp_safe_out                         true
% 2.34/0.98  --problem_path                          ""
% 2.34/0.98  --include_path                          ""
% 2.34/0.98  --clausifier                            res/vclausify_rel
% 2.34/0.98  --clausifier_options                    --mode clausify
% 2.34/0.98  --stdin                                 false
% 2.34/0.98  --stats_out                             all
% 2.34/0.98  
% 2.34/0.98  ------ General Options
% 2.34/0.98  
% 2.34/0.98  --fof                                   false
% 2.34/0.98  --time_out_real                         305.
% 2.34/0.98  --time_out_virtual                      -1.
% 2.34/0.98  --symbol_type_check                     false
% 2.34/0.98  --clausify_out                          false
% 2.34/0.98  --sig_cnt_out                           false
% 2.34/0.99  --trig_cnt_out                          false
% 2.34/0.99  --trig_cnt_out_tolerance                1.
% 2.34/0.99  --trig_cnt_out_sk_spl                   false
% 2.34/0.99  --abstr_cl_out                          false
% 2.34/0.99  
% 2.34/0.99  ------ Global Options
% 2.34/0.99  
% 2.34/0.99  --schedule                              default
% 2.34/0.99  --add_important_lit                     false
% 2.34/0.99  --prop_solver_per_cl                    1000
% 2.34/0.99  --min_unsat_core                        false
% 2.34/0.99  --soft_assumptions                      false
% 2.34/0.99  --soft_lemma_size                       3
% 2.34/0.99  --prop_impl_unit_size                   0
% 2.34/0.99  --prop_impl_unit                        []
% 2.34/0.99  --share_sel_clauses                     true
% 2.34/0.99  --reset_solvers                         false
% 2.34/0.99  --bc_imp_inh                            [conj_cone]
% 2.34/0.99  --conj_cone_tolerance                   3.
% 2.34/0.99  --extra_neg_conj                        none
% 2.34/0.99  --large_theory_mode                     true
% 2.34/0.99  --prolific_symb_bound                   200
% 2.34/0.99  --lt_threshold                          2000
% 2.34/0.99  --clause_weak_htbl                      true
% 2.34/0.99  --gc_record_bc_elim                     false
% 2.34/0.99  
% 2.34/0.99  ------ Preprocessing Options
% 2.34/0.99  
% 2.34/0.99  --preprocessing_flag                    true
% 2.34/0.99  --time_out_prep_mult                    0.1
% 2.34/0.99  --splitting_mode                        input
% 2.34/0.99  --splitting_grd                         true
% 2.34/0.99  --splitting_cvd                         false
% 2.34/0.99  --splitting_cvd_svl                     false
% 2.34/0.99  --splitting_nvd                         32
% 2.34/0.99  --sub_typing                            true
% 2.34/0.99  --prep_gs_sim                           true
% 2.34/0.99  --prep_unflatten                        true
% 2.34/0.99  --prep_res_sim                          true
% 2.34/0.99  --prep_upred                            true
% 2.34/0.99  --prep_sem_filter                       exhaustive
% 2.34/0.99  --prep_sem_filter_out                   false
% 2.34/0.99  --pred_elim                             true
% 2.34/0.99  --res_sim_input                         true
% 2.34/0.99  --eq_ax_congr_red                       true
% 2.34/0.99  --pure_diseq_elim                       true
% 2.34/0.99  --brand_transform                       false
% 2.34/0.99  --non_eq_to_eq                          false
% 2.34/0.99  --prep_def_merge                        true
% 2.34/0.99  --prep_def_merge_prop_impl              false
% 2.34/0.99  --prep_def_merge_mbd                    true
% 2.34/0.99  --prep_def_merge_tr_red                 false
% 2.34/0.99  --prep_def_merge_tr_cl                  false
% 2.34/0.99  --smt_preprocessing                     true
% 2.34/0.99  --smt_ac_axioms                         fast
% 2.34/0.99  --preprocessed_out                      false
% 2.34/0.99  --preprocessed_stats                    false
% 2.34/0.99  
% 2.34/0.99  ------ Abstraction refinement Options
% 2.34/0.99  
% 2.34/0.99  --abstr_ref                             []
% 2.34/0.99  --abstr_ref_prep                        false
% 2.34/0.99  --abstr_ref_until_sat                   false
% 2.34/0.99  --abstr_ref_sig_restrict                funpre
% 2.34/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/0.99  --abstr_ref_under                       []
% 2.34/0.99  
% 2.34/0.99  ------ SAT Options
% 2.34/0.99  
% 2.34/0.99  --sat_mode                              false
% 2.34/0.99  --sat_fm_restart_options                ""
% 2.34/0.99  --sat_gr_def                            false
% 2.34/0.99  --sat_epr_types                         true
% 2.34/0.99  --sat_non_cyclic_types                  false
% 2.34/0.99  --sat_finite_models                     false
% 2.34/0.99  --sat_fm_lemmas                         false
% 2.34/0.99  --sat_fm_prep                           false
% 2.34/0.99  --sat_fm_uc_incr                        true
% 2.34/0.99  --sat_out_model                         small
% 2.34/0.99  --sat_out_clauses                       false
% 2.34/0.99  
% 2.34/0.99  ------ QBF Options
% 2.34/0.99  
% 2.34/0.99  --qbf_mode                              false
% 2.34/0.99  --qbf_elim_univ                         false
% 2.34/0.99  --qbf_dom_inst                          none
% 2.34/0.99  --qbf_dom_pre_inst                      false
% 2.34/0.99  --qbf_sk_in                             false
% 2.34/0.99  --qbf_pred_elim                         true
% 2.34/0.99  --qbf_split                             512
% 2.34/0.99  
% 2.34/0.99  ------ BMC1 Options
% 2.34/0.99  
% 2.34/0.99  --bmc1_incremental                      false
% 2.34/0.99  --bmc1_axioms                           reachable_all
% 2.34/0.99  --bmc1_min_bound                        0
% 2.34/0.99  --bmc1_max_bound                        -1
% 2.34/0.99  --bmc1_max_bound_default                -1
% 2.34/0.99  --bmc1_symbol_reachability              true
% 2.34/0.99  --bmc1_property_lemmas                  false
% 2.34/0.99  --bmc1_k_induction                      false
% 2.34/0.99  --bmc1_non_equiv_states                 false
% 2.34/0.99  --bmc1_deadlock                         false
% 2.34/0.99  --bmc1_ucm                              false
% 2.34/0.99  --bmc1_add_unsat_core                   none
% 2.34/0.99  --bmc1_unsat_core_children              false
% 2.34/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/0.99  --bmc1_out_stat                         full
% 2.34/0.99  --bmc1_ground_init                      false
% 2.34/0.99  --bmc1_pre_inst_next_state              false
% 2.34/0.99  --bmc1_pre_inst_state                   false
% 2.34/0.99  --bmc1_pre_inst_reach_state             false
% 2.34/0.99  --bmc1_out_unsat_core                   false
% 2.34/0.99  --bmc1_aig_witness_out                  false
% 2.34/0.99  --bmc1_verbose                          false
% 2.34/0.99  --bmc1_dump_clauses_tptp                false
% 2.34/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.34/0.99  --bmc1_dump_file                        -
% 2.34/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.34/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.34/0.99  --bmc1_ucm_extend_mode                  1
% 2.34/0.99  --bmc1_ucm_init_mode                    2
% 2.34/0.99  --bmc1_ucm_cone_mode                    none
% 2.34/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.34/0.99  --bmc1_ucm_relax_model                  4
% 2.34/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.34/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/0.99  --bmc1_ucm_layered_model                none
% 2.34/0.99  --bmc1_ucm_max_lemma_size               10
% 2.34/0.99  
% 2.34/0.99  ------ AIG Options
% 2.34/0.99  
% 2.34/0.99  --aig_mode                              false
% 2.34/0.99  
% 2.34/0.99  ------ Instantiation Options
% 2.34/0.99  
% 2.34/0.99  --instantiation_flag                    true
% 2.34/0.99  --inst_sos_flag                         false
% 2.34/0.99  --inst_sos_phase                        true
% 2.34/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/0.99  --inst_lit_sel_side                     num_symb
% 2.34/0.99  --inst_solver_per_active                1400
% 2.34/0.99  --inst_solver_calls_frac                1.
% 2.34/0.99  --inst_passive_queue_type               priority_queues
% 2.34/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/0.99  --inst_passive_queues_freq              [25;2]
% 2.34/0.99  --inst_dismatching                      true
% 2.34/0.99  --inst_eager_unprocessed_to_passive     true
% 2.34/0.99  --inst_prop_sim_given                   true
% 2.34/0.99  --inst_prop_sim_new                     false
% 2.34/0.99  --inst_subs_new                         false
% 2.34/0.99  --inst_eq_res_simp                      false
% 2.34/0.99  --inst_subs_given                       false
% 2.34/0.99  --inst_orphan_elimination               true
% 2.34/0.99  --inst_learning_loop_flag               true
% 2.34/0.99  --inst_learning_start                   3000
% 2.34/0.99  --inst_learning_factor                  2
% 2.34/0.99  --inst_start_prop_sim_after_learn       3
% 2.34/0.99  --inst_sel_renew                        solver
% 2.34/0.99  --inst_lit_activity_flag                true
% 2.34/0.99  --inst_restr_to_given                   false
% 2.34/0.99  --inst_activity_threshold               500
% 2.34/0.99  --inst_out_proof                        true
% 2.34/0.99  
% 2.34/0.99  ------ Resolution Options
% 2.34/0.99  
% 2.34/0.99  --resolution_flag                       true
% 2.34/0.99  --res_lit_sel                           adaptive
% 2.34/0.99  --res_lit_sel_side                      none
% 2.34/0.99  --res_ordering                          kbo
% 2.34/0.99  --res_to_prop_solver                    active
% 2.34/0.99  --res_prop_simpl_new                    false
% 2.34/0.99  --res_prop_simpl_given                  true
% 2.34/0.99  --res_passive_queue_type                priority_queues
% 2.34/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/0.99  --res_passive_queues_freq               [15;5]
% 2.34/0.99  --res_forward_subs                      full
% 2.34/0.99  --res_backward_subs                     full
% 2.34/0.99  --res_forward_subs_resolution           true
% 2.34/0.99  --res_backward_subs_resolution          true
% 2.34/0.99  --res_orphan_elimination                true
% 2.34/0.99  --res_time_limit                        2.
% 2.34/0.99  --res_out_proof                         true
% 2.34/0.99  
% 2.34/0.99  ------ Superposition Options
% 2.34/0.99  
% 2.34/0.99  --superposition_flag                    true
% 2.34/0.99  --sup_passive_queue_type                priority_queues
% 2.34/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.34/0.99  --demod_completeness_check              fast
% 2.34/0.99  --demod_use_ground                      true
% 2.34/0.99  --sup_to_prop_solver                    passive
% 2.34/0.99  --sup_prop_simpl_new                    true
% 2.34/0.99  --sup_prop_simpl_given                  true
% 2.34/0.99  --sup_fun_splitting                     false
% 2.34/0.99  --sup_smt_interval                      50000
% 2.34/0.99  
% 2.34/0.99  ------ Superposition Simplification Setup
% 2.34/0.99  
% 2.34/0.99  --sup_indices_passive                   []
% 2.34/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_full_bw                           [BwDemod]
% 2.34/0.99  --sup_immed_triv                        [TrivRules]
% 2.34/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_immed_bw_main                     []
% 2.34/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.99  
% 2.34/0.99  ------ Combination Options
% 2.34/0.99  
% 2.34/0.99  --comb_res_mult                         3
% 2.34/0.99  --comb_sup_mult                         2
% 2.34/0.99  --comb_inst_mult                        10
% 2.34/0.99  
% 2.34/0.99  ------ Debug Options
% 2.34/0.99  
% 2.34/0.99  --dbg_backtrace                         false
% 2.34/0.99  --dbg_dump_prop_clauses                 false
% 2.34/0.99  --dbg_dump_prop_clauses_file            -
% 2.34/0.99  --dbg_out_stat                          false
% 2.34/0.99  ------ Parsing...
% 2.34/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.34/0.99  
% 2.34/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.34/0.99  
% 2.34/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.34/0.99  
% 2.34/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.34/0.99  ------ Proving...
% 2.34/0.99  ------ Problem Properties 
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  clauses                                 29
% 2.34/0.99  conjectures                             10
% 2.34/0.99  EPR                                     4
% 2.34/0.99  Horn                                    27
% 2.34/0.99  unary                                   8
% 2.34/0.99  binary                                  4
% 2.34/0.99  lits                                    101
% 2.34/0.99  lits eq                                 3
% 2.34/0.99  fd_pure                                 0
% 2.34/0.99  fd_pseudo                               0
% 2.34/0.99  fd_cond                                 0
% 2.34/0.99  fd_pseudo_cond                          0
% 2.34/0.99  AC symbols                              0
% 2.34/0.99  
% 2.34/0.99  ------ Schedule dynamic 5 is on 
% 2.34/0.99  
% 2.34/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  ------ 
% 2.34/0.99  Current options:
% 2.34/0.99  ------ 
% 2.34/0.99  
% 2.34/0.99  ------ Input Options
% 2.34/0.99  
% 2.34/0.99  --out_options                           all
% 2.34/0.99  --tptp_safe_out                         true
% 2.34/0.99  --problem_path                          ""
% 2.34/0.99  --include_path                          ""
% 2.34/0.99  --clausifier                            res/vclausify_rel
% 2.34/0.99  --clausifier_options                    --mode clausify
% 2.34/0.99  --stdin                                 false
% 2.34/0.99  --stats_out                             all
% 2.34/0.99  
% 2.34/0.99  ------ General Options
% 2.34/0.99  
% 2.34/0.99  --fof                                   false
% 2.34/0.99  --time_out_real                         305.
% 2.34/0.99  --time_out_virtual                      -1.
% 2.34/0.99  --symbol_type_check                     false
% 2.34/0.99  --clausify_out                          false
% 2.34/0.99  --sig_cnt_out                           false
% 2.34/0.99  --trig_cnt_out                          false
% 2.34/0.99  --trig_cnt_out_tolerance                1.
% 2.34/0.99  --trig_cnt_out_sk_spl                   false
% 2.34/0.99  --abstr_cl_out                          false
% 2.34/0.99  
% 2.34/0.99  ------ Global Options
% 2.34/0.99  
% 2.34/0.99  --schedule                              default
% 2.34/0.99  --add_important_lit                     false
% 2.34/0.99  --prop_solver_per_cl                    1000
% 2.34/0.99  --min_unsat_core                        false
% 2.34/0.99  --soft_assumptions                      false
% 2.34/0.99  --soft_lemma_size                       3
% 2.34/0.99  --prop_impl_unit_size                   0
% 2.34/0.99  --prop_impl_unit                        []
% 2.34/0.99  --share_sel_clauses                     true
% 2.34/0.99  --reset_solvers                         false
% 2.34/0.99  --bc_imp_inh                            [conj_cone]
% 2.34/0.99  --conj_cone_tolerance                   3.
% 2.34/0.99  --extra_neg_conj                        none
% 2.34/0.99  --large_theory_mode                     true
% 2.34/0.99  --prolific_symb_bound                   200
% 2.34/0.99  --lt_threshold                          2000
% 2.34/0.99  --clause_weak_htbl                      true
% 2.34/0.99  --gc_record_bc_elim                     false
% 2.34/0.99  
% 2.34/0.99  ------ Preprocessing Options
% 2.34/0.99  
% 2.34/0.99  --preprocessing_flag                    true
% 2.34/0.99  --time_out_prep_mult                    0.1
% 2.34/0.99  --splitting_mode                        input
% 2.34/0.99  --splitting_grd                         true
% 2.34/0.99  --splitting_cvd                         false
% 2.34/0.99  --splitting_cvd_svl                     false
% 2.34/0.99  --splitting_nvd                         32
% 2.34/0.99  --sub_typing                            true
% 2.34/0.99  --prep_gs_sim                           true
% 2.34/0.99  --prep_unflatten                        true
% 2.34/0.99  --prep_res_sim                          true
% 2.34/0.99  --prep_upred                            true
% 2.34/0.99  --prep_sem_filter                       exhaustive
% 2.34/0.99  --prep_sem_filter_out                   false
% 2.34/0.99  --pred_elim                             true
% 2.34/0.99  --res_sim_input                         true
% 2.34/0.99  --eq_ax_congr_red                       true
% 2.34/0.99  --pure_diseq_elim                       true
% 2.34/0.99  --brand_transform                       false
% 2.34/0.99  --non_eq_to_eq                          false
% 2.34/0.99  --prep_def_merge                        true
% 2.34/0.99  --prep_def_merge_prop_impl              false
% 2.34/0.99  --prep_def_merge_mbd                    true
% 2.34/0.99  --prep_def_merge_tr_red                 false
% 2.34/0.99  --prep_def_merge_tr_cl                  false
% 2.34/0.99  --smt_preprocessing                     true
% 2.34/0.99  --smt_ac_axioms                         fast
% 2.34/0.99  --preprocessed_out                      false
% 2.34/0.99  --preprocessed_stats                    false
% 2.34/0.99  
% 2.34/0.99  ------ Abstraction refinement Options
% 2.34/0.99  
% 2.34/0.99  --abstr_ref                             []
% 2.34/0.99  --abstr_ref_prep                        false
% 2.34/0.99  --abstr_ref_until_sat                   false
% 2.34/0.99  --abstr_ref_sig_restrict                funpre
% 2.34/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/0.99  --abstr_ref_under                       []
% 2.34/0.99  
% 2.34/0.99  ------ SAT Options
% 2.34/0.99  
% 2.34/0.99  --sat_mode                              false
% 2.34/0.99  --sat_fm_restart_options                ""
% 2.34/0.99  --sat_gr_def                            false
% 2.34/0.99  --sat_epr_types                         true
% 2.34/0.99  --sat_non_cyclic_types                  false
% 2.34/0.99  --sat_finite_models                     false
% 2.34/0.99  --sat_fm_lemmas                         false
% 2.34/0.99  --sat_fm_prep                           false
% 2.34/0.99  --sat_fm_uc_incr                        true
% 2.34/0.99  --sat_out_model                         small
% 2.34/0.99  --sat_out_clauses                       false
% 2.34/0.99  
% 2.34/0.99  ------ QBF Options
% 2.34/0.99  
% 2.34/0.99  --qbf_mode                              false
% 2.34/0.99  --qbf_elim_univ                         false
% 2.34/0.99  --qbf_dom_inst                          none
% 2.34/0.99  --qbf_dom_pre_inst                      false
% 2.34/0.99  --qbf_sk_in                             false
% 2.34/0.99  --qbf_pred_elim                         true
% 2.34/0.99  --qbf_split                             512
% 2.34/0.99  
% 2.34/0.99  ------ BMC1 Options
% 2.34/0.99  
% 2.34/0.99  --bmc1_incremental                      false
% 2.34/0.99  --bmc1_axioms                           reachable_all
% 2.34/0.99  --bmc1_min_bound                        0
% 2.34/0.99  --bmc1_max_bound                        -1
% 2.34/0.99  --bmc1_max_bound_default                -1
% 2.34/0.99  --bmc1_symbol_reachability              true
% 2.34/0.99  --bmc1_property_lemmas                  false
% 2.34/0.99  --bmc1_k_induction                      false
% 2.34/0.99  --bmc1_non_equiv_states                 false
% 2.34/0.99  --bmc1_deadlock                         false
% 2.34/0.99  --bmc1_ucm                              false
% 2.34/0.99  --bmc1_add_unsat_core                   none
% 2.34/0.99  --bmc1_unsat_core_children              false
% 2.34/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/0.99  --bmc1_out_stat                         full
% 2.34/0.99  --bmc1_ground_init                      false
% 2.34/0.99  --bmc1_pre_inst_next_state              false
% 2.34/0.99  --bmc1_pre_inst_state                   false
% 2.34/0.99  --bmc1_pre_inst_reach_state             false
% 2.34/0.99  --bmc1_out_unsat_core                   false
% 2.34/0.99  --bmc1_aig_witness_out                  false
% 2.34/0.99  --bmc1_verbose                          false
% 2.34/0.99  --bmc1_dump_clauses_tptp                false
% 2.34/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.34/0.99  --bmc1_dump_file                        -
% 2.34/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.34/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.34/0.99  --bmc1_ucm_extend_mode                  1
% 2.34/0.99  --bmc1_ucm_init_mode                    2
% 2.34/0.99  --bmc1_ucm_cone_mode                    none
% 2.34/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.34/0.99  --bmc1_ucm_relax_model                  4
% 2.34/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.34/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/0.99  --bmc1_ucm_layered_model                none
% 2.34/0.99  --bmc1_ucm_max_lemma_size               10
% 2.34/0.99  
% 2.34/0.99  ------ AIG Options
% 2.34/0.99  
% 2.34/0.99  --aig_mode                              false
% 2.34/0.99  
% 2.34/0.99  ------ Instantiation Options
% 2.34/0.99  
% 2.34/0.99  --instantiation_flag                    true
% 2.34/0.99  --inst_sos_flag                         false
% 2.34/0.99  --inst_sos_phase                        true
% 2.34/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/0.99  --inst_lit_sel_side                     none
% 2.34/0.99  --inst_solver_per_active                1400
% 2.34/0.99  --inst_solver_calls_frac                1.
% 2.34/0.99  --inst_passive_queue_type               priority_queues
% 2.34/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/0.99  --inst_passive_queues_freq              [25;2]
% 2.34/0.99  --inst_dismatching                      true
% 2.34/0.99  --inst_eager_unprocessed_to_passive     true
% 2.34/0.99  --inst_prop_sim_given                   true
% 2.34/0.99  --inst_prop_sim_new                     false
% 2.34/0.99  --inst_subs_new                         false
% 2.34/0.99  --inst_eq_res_simp                      false
% 2.34/0.99  --inst_subs_given                       false
% 2.34/0.99  --inst_orphan_elimination               true
% 2.34/0.99  --inst_learning_loop_flag               true
% 2.34/0.99  --inst_learning_start                   3000
% 2.34/0.99  --inst_learning_factor                  2
% 2.34/0.99  --inst_start_prop_sim_after_learn       3
% 2.34/0.99  --inst_sel_renew                        solver
% 2.34/0.99  --inst_lit_activity_flag                true
% 2.34/0.99  --inst_restr_to_given                   false
% 2.34/0.99  --inst_activity_threshold               500
% 2.34/0.99  --inst_out_proof                        true
% 2.34/0.99  
% 2.34/0.99  ------ Resolution Options
% 2.34/0.99  
% 2.34/0.99  --resolution_flag                       false
% 2.34/0.99  --res_lit_sel                           adaptive
% 2.34/0.99  --res_lit_sel_side                      none
% 2.34/0.99  --res_ordering                          kbo
% 2.34/0.99  --res_to_prop_solver                    active
% 2.34/0.99  --res_prop_simpl_new                    false
% 2.34/0.99  --res_prop_simpl_given                  true
% 2.34/0.99  --res_passive_queue_type                priority_queues
% 2.34/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/0.99  --res_passive_queues_freq               [15;5]
% 2.34/0.99  --res_forward_subs                      full
% 2.34/0.99  --res_backward_subs                     full
% 2.34/0.99  --res_forward_subs_resolution           true
% 2.34/0.99  --res_backward_subs_resolution          true
% 2.34/0.99  --res_orphan_elimination                true
% 2.34/0.99  --res_time_limit                        2.
% 2.34/0.99  --res_out_proof                         true
% 2.34/0.99  
% 2.34/0.99  ------ Superposition Options
% 2.34/0.99  
% 2.34/0.99  --superposition_flag                    true
% 2.34/0.99  --sup_passive_queue_type                priority_queues
% 2.34/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.34/0.99  --demod_completeness_check              fast
% 2.34/0.99  --demod_use_ground                      true
% 2.34/0.99  --sup_to_prop_solver                    passive
% 2.34/0.99  --sup_prop_simpl_new                    true
% 2.34/0.99  --sup_prop_simpl_given                  true
% 2.34/0.99  --sup_fun_splitting                     false
% 2.34/0.99  --sup_smt_interval                      50000
% 2.34/0.99  
% 2.34/0.99  ------ Superposition Simplification Setup
% 2.34/0.99  
% 2.34/0.99  --sup_indices_passive                   []
% 2.34/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_full_bw                           [BwDemod]
% 2.34/0.99  --sup_immed_triv                        [TrivRules]
% 2.34/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_immed_bw_main                     []
% 2.34/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.99  
% 2.34/0.99  ------ Combination Options
% 2.34/0.99  
% 2.34/0.99  --comb_res_mult                         3
% 2.34/0.99  --comb_sup_mult                         2
% 2.34/0.99  --comb_inst_mult                        10
% 2.34/0.99  
% 2.34/0.99  ------ Debug Options
% 2.34/0.99  
% 2.34/0.99  --dbg_backtrace                         false
% 2.34/0.99  --dbg_dump_prop_clauses                 false
% 2.34/0.99  --dbg_dump_prop_clauses_file            -
% 2.34/0.99  --dbg_out_stat                          false
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  ------ Proving...
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  % SZS status Theorem for theBenchmark.p
% 2.34/0.99  
% 2.34/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.34/0.99  
% 2.34/0.99  fof(f4,conjecture,(
% 2.34/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f5,negated_conjecture,(
% 2.34/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.34/0.99    inference(negated_conjecture,[],[f4])).
% 2.34/0.99  
% 2.34/0.99  fof(f11,plain,(
% 2.34/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.34/0.99    inference(ennf_transformation,[],[f5])).
% 2.34/0.99  
% 2.34/0.99  fof(f12,plain,(
% 2.34/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.34/0.99    inference(flattening,[],[f11])).
% 2.34/0.99  
% 2.34/0.99  fof(f22,plain,(
% 2.34/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5))) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.34/0.99    inference(nnf_transformation,[],[f12])).
% 2.34/0.99  
% 2.34/0.99  fof(f23,plain,(
% 2.34/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.34/0.99    inference(flattening,[],[f22])).
% 2.34/0.99  
% 2.34/0.99  fof(f30,plain,(
% 2.34/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8) | r1_tmap_1(X1,X0,X2,X5)) & sK8 = X5 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(sK8,u1_struct_0(X3)))) )),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f29,plain,(
% 2.34/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,sK7)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,sK7)) & sK7 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(sK7,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK7,u1_struct_0(X1)))) )),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f28,plain,(
% 2.34/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(sK6,u1_struct_0(X3)) & r2_hidden(X5,sK6) & v3_pre_topc(sK6,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f27,plain,(
% 2.34/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(sK5)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK5,X1) & ~v2_struct_0(sK5))) )),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f26,plain,(
% 2.34/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X6) | ~r1_tmap_1(X1,X0,sK4,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X6) | r1_tmap_1(X1,X0,sK4,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f25,plain,(
% 2.34/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X6) | ~r1_tmap_1(sK3,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X6) | r1_tmap_1(sK3,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK3) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f24,plain,(
% 2.34/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6) | ~r1_tmap_1(X1,sK2,X2,X5)) & (r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6) | r1_tmap_1(X1,sK2,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f31,plain,(
% 2.34/0.99    (((((((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | ~r1_tmap_1(sK3,sK2,sK4,sK7)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | r1_tmap_1(sK3,sK2,sK4,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK5)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK3) & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.34/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f23,f30,f29,f28,f27,f26,f25,f24])).
% 2.34/0.99  
% 2.34/0.99  fof(f49,plain,(
% 2.34/0.99    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f3,axiom,(
% 2.34/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f9,plain,(
% 2.34/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.34/0.99    inference(ennf_transformation,[],[f3])).
% 2.34/0.99  
% 2.34/0.99  fof(f10,plain,(
% 2.34/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/0.99    inference(flattening,[],[f9])).
% 2.34/0.99  
% 2.34/0.99  fof(f21,plain,(
% 2.34/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/0.99    inference(nnf_transformation,[],[f10])).
% 2.34/0.99  
% 2.34/0.99  fof(f41,plain,(
% 2.34/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.99    inference(cnf_transformation,[],[f21])).
% 2.34/0.99  
% 2.34/0.99  fof(f62,plain,(
% 2.34/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.99    inference(equality_resolution,[],[f41])).
% 2.34/0.99  
% 2.34/0.99  fof(f52,plain,(
% 2.34/0.99    m1_pre_topc(sK5,sK3)),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f45,plain,(
% 2.34/0.99    ~v2_struct_0(sK3)),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f46,plain,(
% 2.34/0.99    v2_pre_topc(sK3)),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f47,plain,(
% 2.34/0.99    l1_pre_topc(sK3)),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f51,plain,(
% 2.34/0.99    ~v2_struct_0(sK5)),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f48,plain,(
% 2.34/0.99    v1_funct_1(sK4)),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f44,plain,(
% 2.34/0.99    l1_pre_topc(sK2)),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f42,plain,(
% 2.34/0.99    ~v2_struct_0(sK2)),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f43,plain,(
% 2.34/0.99    v2_pre_topc(sK2)),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f50,plain,(
% 2.34/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f40,plain,(
% 2.34/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.99    inference(cnf_transformation,[],[f21])).
% 2.34/0.99  
% 2.34/0.99  fof(f63,plain,(
% 2.34/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.99    inference(equality_resolution,[],[f40])).
% 2.34/0.99  
% 2.34/0.99  fof(f1,axiom,(
% 2.34/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f6,plain,(
% 2.34/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.34/0.99    inference(ennf_transformation,[],[f1])).
% 2.34/0.99  
% 2.34/0.99  fof(f13,plain,(
% 2.34/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.34/0.99    inference(nnf_transformation,[],[f6])).
% 2.34/0.99  
% 2.34/0.99  fof(f14,plain,(
% 2.34/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.34/0.99    inference(rectify,[],[f13])).
% 2.34/0.99  
% 2.34/0.99  fof(f15,plain,(
% 2.34/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f16,plain,(
% 2.34/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.34/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 2.34/0.99  
% 2.34/0.99  fof(f33,plain,(
% 2.34/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.34/0.99    inference(cnf_transformation,[],[f16])).
% 2.34/0.99  
% 2.34/0.99  fof(f34,plain,(
% 2.34/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.34/0.99    inference(cnf_transformation,[],[f16])).
% 2.34/0.99  
% 2.34/0.99  fof(f2,axiom,(
% 2.34/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 2.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f7,plain,(
% 2.34/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.34/0.99    inference(ennf_transformation,[],[f2])).
% 2.34/0.99  
% 2.34/0.99  fof(f8,plain,(
% 2.34/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/0.99    inference(flattening,[],[f7])).
% 2.34/0.99  
% 2.34/0.99  fof(f17,plain,(
% 2.34/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/0.99    inference(nnf_transformation,[],[f8])).
% 2.34/0.99  
% 2.34/0.99  fof(f18,plain,(
% 2.34/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/0.99    inference(rectify,[],[f17])).
% 2.34/0.99  
% 2.34/0.99  fof(f19,plain,(
% 2.34/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f20,plain,(
% 2.34/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).
% 2.34/0.99  
% 2.34/0.99  fof(f39,plain,(
% 2.34/0.99    ( ! [X2,X0,X3,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.99    inference(cnf_transformation,[],[f20])).
% 2.34/0.99  
% 2.34/0.99  fof(f59,plain,(
% 2.34/0.99    sK7 = sK8),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f61,plain,(
% 2.34/0.99    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | ~r1_tmap_1(sK3,sK2,sK4,sK7)),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f60,plain,(
% 2.34/0.99    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | r1_tmap_1(sK3,sK2,sK4,sK7)),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f58,plain,(
% 2.34/0.99    r1_tarski(sK6,u1_struct_0(sK5))),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f57,plain,(
% 2.34/0.99    r2_hidden(sK7,sK6)),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f56,plain,(
% 2.34/0.99    v3_pre_topc(sK6,sK3)),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f55,plain,(
% 2.34/0.99    m1_subset_1(sK8,u1_struct_0(sK5))),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f54,plain,(
% 2.34/0.99    m1_subset_1(sK7,u1_struct_0(sK3))),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f53,plain,(
% 2.34/0.99    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.34/0.99    inference(cnf_transformation,[],[f31])).
% 2.34/0.99  
% 2.34/0.99  cnf(c_6529,plain,
% 2.34/0.99      ( ~ r1_tmap_1(X0_53,X1_53,X0_54,X1_54)
% 2.34/0.99      | r1_tmap_1(X0_53,X1_53,X2_54,X3_54)
% 2.34/0.99      | X2_54 != X0_54
% 2.34/0.99      | X3_54 != X1_54 ),
% 2.34/0.99      theory(equality) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_8276,plain,
% 2.34/0.99      ( r1_tmap_1(sK5,sK2,X0_54,X1_54)
% 2.34/0.99      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.34/0.99      | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.34/0.99      | X1_54 != sK7 ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_6529]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_8756,plain,
% 2.34/0.99      ( r1_tmap_1(sK5,sK2,X0_54,sK8)
% 2.34/0.99      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.34/0.99      | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.34/0.99      | sK8 != sK7 ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_8276]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_9083,plain,
% 2.34/0.99      ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.34/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 2.34/0.99      | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.34/0.99      | sK8 != sK7 ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_8756]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_22,negated_conjecture,
% 2.34/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 2.34/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_8,plain,
% 2.34/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.34/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.34/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.34/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.34/0.99      | ~ m1_pre_topc(X4,X0)
% 2.34/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.34/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.34/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.34/0.99      | ~ v1_funct_1(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(X4)
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X0) ),
% 2.34/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_19,negated_conjecture,
% 2.34/0.99      ( m1_pre_topc(sK5,sK3) ),
% 2.34/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_492,plain,
% 2.34/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.34/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.34/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.34/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.34/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.34/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.34/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.34/0.99      | ~ v1_funct_1(X2)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X4)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X0)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | sK3 != X0
% 2.34/0.99      | sK5 != X4 ),
% 2.34/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_493,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,X0,X1,X2)
% 2.34/0.99      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 2.34/0.99      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 2.34/0.99      | ~ m1_connsp_2(X3,sK3,X2)
% 2.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 2.34/0.99      | ~ v1_funct_1(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(sK3)
% 2.34/0.99      | v2_struct_0(sK5)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | ~ v2_pre_topc(sK3)
% 2.34/0.99      | ~ l1_pre_topc(X0)
% 2.34/0.99      | ~ l1_pre_topc(sK3) ),
% 2.34/0.99      inference(unflattening,[status(thm)],[c_492]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_26,negated_conjecture,
% 2.34/0.99      ( ~ v2_struct_0(sK3) ),
% 2.34/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_25,negated_conjecture,
% 2.34/0.99      ( v2_pre_topc(sK3) ),
% 2.34/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_24,negated_conjecture,
% 2.34/0.99      ( l1_pre_topc(sK3) ),
% 2.34/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_20,negated_conjecture,
% 2.34/0.99      ( ~ v2_struct_0(sK5) ),
% 2.34/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_497,plain,
% 2.34/0.99      ( ~ l1_pre_topc(X0)
% 2.34/0.99      | r1_tmap_1(sK3,X0,X1,X2)
% 2.34/0.99      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 2.34/0.99      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 2.34/0.99      | ~ m1_connsp_2(X3,sK3,X2)
% 2.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 2.34/0.99      | ~ v1_funct_1(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | ~ v2_pre_topc(X0) ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_493,c_26,c_25,c_24,c_20]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_498,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,X0,X1,X2)
% 2.34/0.99      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 2.34/0.99      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 2.34/0.99      | ~ m1_connsp_2(X3,sK3,X2)
% 2.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 2.34/0.99      | ~ v1_funct_1(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | ~ l1_pre_topc(X0) ),
% 2.34/0.99      inference(renaming,[status(thm)],[c_497]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_545,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,X0,X1,X2)
% 2.34/0.99      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 2.34/0.99      | ~ m1_connsp_2(X3,sK3,X2)
% 2.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 2.34/0.99      | ~ v1_funct_1(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | ~ l1_pre_topc(X0)
% 2.34/0.99      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.34/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.34/0.99      | sK4 != X1 ),
% 2.34/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_498]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_546,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.34/0.99      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.34/0.99      | ~ m1_connsp_2(X2,sK3,X1)
% 2.34/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.34/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.34/0.99      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.34/0.99      | ~ v1_funct_1(sK4)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | ~ l1_pre_topc(X0)
% 2.34/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.34/0.99      inference(unflattening,[status(thm)],[c_545]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_23,negated_conjecture,
% 2.34/0.99      ( v1_funct_1(sK4) ),
% 2.34/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_550,plain,
% 2.34/0.99      ( ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.34/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_connsp_2(X2,sK3,X1)
% 2.34/0.99      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.34/0.99      | r1_tmap_1(sK3,X0,sK4,X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | ~ l1_pre_topc(X0)
% 2.34/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_546,c_23]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_551,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.34/0.99      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.34/0.99      | ~ m1_connsp_2(X2,sK3,X1)
% 2.34/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.34/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.34/0.99      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | ~ l1_pre_topc(X0)
% 2.34/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.34/0.99      inference(renaming,[status(thm)],[c_550]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_27,negated_conjecture,
% 2.34/0.99      ( l1_pre_topc(sK2) ),
% 2.34/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1047,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.34/0.99      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.34/0.99      | ~ m1_connsp_2(X2,sK3,X1)
% 2.34/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.34/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.34/0.99      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.34/0.99      | sK2 != X0 ),
% 2.34/0.99      inference(resolution_lifted,[status(thm)],[c_551,c_27]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1048,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.34/0.99      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.34/0.99      | ~ m1_connsp_2(X1,sK3,X0)
% 2.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.34/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 2.34/0.99      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.34/0.99      | v2_struct_0(sK2)
% 2.34/0.99      | ~ v2_pre_topc(sK2)
% 2.34/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.34/0.99      inference(unflattening,[status(thm)],[c_1047]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_29,negated_conjecture,
% 2.34/0.99      ( ~ v2_struct_0(sK2) ),
% 2.34/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_28,negated_conjecture,
% 2.34/0.99      ( v2_pre_topc(sK2) ),
% 2.34/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_21,negated_conjecture,
% 2.34/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 2.34/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1052,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.34/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_connsp_2(X1,sK3,X0)
% 2.34/0.99      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.34/0.99      | r1_tmap_1(sK3,sK2,sK4,X0)
% 2.34/0.99      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.34/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_1048,c_29,c_28,c_21]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1053,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.34/0.99      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.34/0.99      | ~ m1_connsp_2(X1,sK3,X0)
% 2.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.34/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.34/0.99      inference(renaming,[status(thm)],[c_1052]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3943,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.34/0.99      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.34/0.99      | ~ m1_connsp_2(X1,sK3,X0)
% 2.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(X1,u1_struct_0(sK5)) ),
% 2.34/0.99      inference(equality_resolution_simp,[status(thm)],[c_1053]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_6491,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,sK2,sK4,X0_54)
% 2.34/0.99      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
% 2.34/0.99      | ~ m1_connsp_2(X1_54,sK3,X0_54)
% 2.34/0.99      | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(X1_54,u1_struct_0(sK5)) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_3943]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7542,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.34/0.99      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.34/0.99      | ~ m1_connsp_2(X0_54,sK3,sK7)
% 2.34/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(X0_54,u1_struct_0(sK5)) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_6491]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_8410,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.34/0.99      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.34/0.99      | ~ m1_connsp_2(sK6,sK3,sK7)
% 2.34/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(sK6,u1_struct_0(sK5)) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_7542]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_9,plain,
% 2.34/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.34/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.34/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.34/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.34/0.99      | ~ m1_pre_topc(X4,X0)
% 2.34/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.34/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.34/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.34/0.99      | ~ v1_funct_1(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(X4)
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X0) ),
% 2.34/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_441,plain,
% 2.34/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.34/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.34/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.34/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.34/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.34/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.34/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.34/0.99      | ~ v1_funct_1(X2)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X4)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X0)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | sK3 != X0
% 2.34/0.99      | sK5 != X4 ),
% 2.34/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_442,plain,
% 2.34/0.99      ( ~ r1_tmap_1(sK3,X0,X1,X2)
% 2.34/0.99      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 2.34/0.99      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 2.34/0.99      | ~ m1_connsp_2(X3,sK3,X2)
% 2.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 2.34/0.99      | ~ v1_funct_1(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(sK3)
% 2.34/0.99      | v2_struct_0(sK5)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | ~ v2_pre_topc(sK3)
% 2.34/0.99      | ~ l1_pre_topc(X0)
% 2.34/0.99      | ~ l1_pre_topc(sK3) ),
% 2.34/0.99      inference(unflattening,[status(thm)],[c_441]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_446,plain,
% 2.34/0.99      ( ~ l1_pre_topc(X0)
% 2.34/0.99      | ~ r1_tmap_1(sK3,X0,X1,X2)
% 2.34/0.99      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 2.34/0.99      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 2.34/0.99      | ~ m1_connsp_2(X3,sK3,X2)
% 2.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 2.34/0.99      | ~ v1_funct_1(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | ~ v2_pre_topc(X0) ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_442,c_26,c_25,c_24,c_20]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_447,plain,
% 2.34/0.99      ( ~ r1_tmap_1(sK3,X0,X1,X2)
% 2.34/0.99      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 2.34/0.99      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 2.34/0.99      | ~ m1_connsp_2(X3,sK3,X2)
% 2.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 2.34/0.99      | ~ v1_funct_1(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | ~ l1_pre_topc(X0) ),
% 2.34/0.99      inference(renaming,[status(thm)],[c_446]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_593,plain,
% 2.34/0.99      ( ~ r1_tmap_1(sK3,X0,X1,X2)
% 2.34/0.99      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 2.34/0.99      | ~ m1_connsp_2(X3,sK3,X2)
% 2.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 2.34/0.99      | ~ v1_funct_1(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | ~ l1_pre_topc(X0)
% 2.34/0.99      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.34/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.34/0.99      | sK4 != X1 ),
% 2.34/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_447]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_594,plain,
% 2.34/0.99      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.34/0.99      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.34/0.99      | ~ m1_connsp_2(X2,sK3,X1)
% 2.34/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.34/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.34/0.99      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.34/0.99      | ~ v1_funct_1(sK4)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | ~ l1_pre_topc(X0)
% 2.34/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.34/0.99      inference(unflattening,[status(thm)],[c_593]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_598,plain,
% 2.34/0.99      ( ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.34/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_connsp_2(X2,sK3,X1)
% 2.34/0.99      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.34/0.99      | ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | ~ l1_pre_topc(X0)
% 2.34/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_594,c_23]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_599,plain,
% 2.34/0.99      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.34/0.99      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.34/0.99      | ~ m1_connsp_2(X2,sK3,X1)
% 2.34/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.34/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.34/0.99      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | ~ l1_pre_topc(X0)
% 2.34/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.34/0.99      inference(renaming,[status(thm)],[c_598]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1011,plain,
% 2.34/0.99      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.34/0.99      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.34/0.99      | ~ m1_connsp_2(X2,sK3,X1)
% 2.34/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.34/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.34/0.99      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | ~ v2_pre_topc(X0)
% 2.34/0.99      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.34/0.99      | sK2 != X0 ),
% 2.34/0.99      inference(resolution_lifted,[status(thm)],[c_599,c_27]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1012,plain,
% 2.34/0.99      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.34/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.34/0.99      | ~ m1_connsp_2(X1,sK3,X0)
% 2.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.34/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 2.34/0.99      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.34/0.99      | v2_struct_0(sK2)
% 2.34/0.99      | ~ v2_pre_topc(sK2)
% 2.34/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.34/0.99      inference(unflattening,[status(thm)],[c_1011]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1016,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.34/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_connsp_2(X1,sK3,X0)
% 2.34/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.34/0.99      | ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.34/0.99      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.34/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_1012,c_29,c_28,c_21]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1017,plain,
% 2.34/0.99      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.34/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.34/0.99      | ~ m1_connsp_2(X1,sK3,X0)
% 2.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.34/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.34/0.99      inference(renaming,[status(thm)],[c_1016]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3947,plain,
% 2.34/0.99      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.34/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.34/0.99      | ~ m1_connsp_2(X1,sK3,X0)
% 2.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(X1,u1_struct_0(sK5)) ),
% 2.34/0.99      inference(equality_resolution_simp,[status(thm)],[c_1017]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_6490,plain,
% 2.34/0.99      ( ~ r1_tmap_1(sK3,sK2,sK4,X0_54)
% 2.34/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
% 2.34/0.99      | ~ m1_connsp_2(X1_54,sK3,X0_54)
% 2.34/0.99      | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(X1_54,u1_struct_0(sK5)) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_3947]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7537,plain,
% 2.34/0.99      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.34/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.34/0.99      | ~ m1_connsp_2(X0_54,sK3,sK7)
% 2.34/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(X0_54,u1_struct_0(sK5)) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_6490]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_8083,plain,
% 2.34/0.99      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.34/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.34/0.99      | ~ m1_connsp_2(sK6,sK3,sK7)
% 2.34/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 2.34/0.99      | ~ r1_tarski(sK6,u1_struct_0(sK5)) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_7537]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1,plain,
% 2.34/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.34/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_6515,plain,
% 2.34/0.99      ( r2_hidden(sK0(X0_54,X1_54),X0_54) | r1_tarski(X0_54,X1_54) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7679,plain,
% 2.34/0.99      ( r2_hidden(sK0(sK6,X0_54),sK6) | r1_tarski(sK6,X0_54) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_6515]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7933,plain,
% 2.34/0.99      ( r2_hidden(sK0(sK6,sK6),sK6) | r1_tarski(sK6,sK6) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_7679]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_0,plain,
% 2.34/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.34/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_6516,plain,
% 2.34/0.99      ( ~ r2_hidden(sK0(X0_54,X1_54),X1_54) | r1_tarski(X0_54,X1_54) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7678,plain,
% 2.34/0.99      ( ~ r2_hidden(sK0(sK6,X0_54),X0_54) | r1_tarski(sK6,X0_54) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_6516]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7932,plain,
% 2.34/0.99      ( ~ r2_hidden(sK0(sK6,sK6),sK6) | r1_tarski(sK6,sK6) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_7678]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_6523,plain,
% 2.34/0.99      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 2.34/0.99      theory(equality) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7644,plain,
% 2.34/0.99      ( X0_54 != X1_54 | X0_54 = sK7 | sK7 != X1_54 ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_6523]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7809,plain,
% 2.34/0.99      ( X0_54 = sK7 | X0_54 != sK8 | sK7 != sK8 ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_7644]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7865,plain,
% 2.34/0.99      ( sK7 != sK8 | sK8 = sK7 | sK8 != sK8 ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_7809]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3,plain,
% 2.34/0.99      ( m1_connsp_2(X0,X1,X2)
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.34/0.99      | ~ v3_pre_topc(X3,X1)
% 2.34/0.99      | ~ r2_hidden(X2,X3)
% 2.34/0.99      | ~ r1_tarski(X3,X0)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X1) ),
% 2.34/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1179,plain,
% 2.34/0.99      ( m1_connsp_2(X0,X1,X2)
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.34/0.99      | ~ v3_pre_topc(X3,X1)
% 2.34/0.99      | ~ r2_hidden(X2,X3)
% 2.34/0.99      | ~ r1_tarski(X3,X0)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | sK3 != X1 ),
% 2.34/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1180,plain,
% 2.34/0.99      ( m1_connsp_2(X0,sK3,X1)
% 2.34/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.34/0.99      | ~ v3_pre_topc(X2,sK3)
% 2.34/0.99      | ~ r2_hidden(X1,X2)
% 2.34/0.99      | ~ r1_tarski(X2,X0)
% 2.34/0.99      | v2_struct_0(sK3)
% 2.34/0.99      | ~ v2_pre_topc(sK3) ),
% 2.34/0.99      inference(unflattening,[status(thm)],[c_1179]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1184,plain,
% 2.34/0.99      ( m1_connsp_2(X0,sK3,X1)
% 2.34/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.34/0.99      | ~ v3_pre_topc(X2,sK3)
% 2.34/0.99      | ~ r2_hidden(X1,X2)
% 2.34/0.99      | ~ r1_tarski(X2,X0) ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_1180,c_26,c_25]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_6497,plain,
% 2.34/0.99      ( m1_connsp_2(X0_54,sK3,X1_54)
% 2.34/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X2_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 2.34/0.99      | ~ v3_pre_topc(X2_54,sK3)
% 2.34/0.99      | ~ r2_hidden(X1_54,X2_54)
% 2.34/0.99      | ~ r1_tarski(X2_54,X0_54) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_1184]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7532,plain,
% 2.34/0.99      ( m1_connsp_2(X0_54,sK3,X1_54)
% 2.34/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 2.34/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ v3_pre_topc(sK6,sK3)
% 2.34/0.99      | ~ r2_hidden(X1_54,sK6)
% 2.34/0.99      | ~ r1_tarski(sK6,X0_54) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_6497]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7670,plain,
% 2.34/0.99      ( m1_connsp_2(X0_54,sK3,sK7)
% 2.34/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.34/0.99      | ~ v3_pre_topc(sK6,sK3)
% 2.34/0.99      | ~ r2_hidden(sK7,sK6)
% 2.34/0.99      | ~ r1_tarski(sK6,X0_54) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_7532]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7751,plain,
% 2.34/0.99      ( m1_connsp_2(sK6,sK3,sK7)
% 2.34/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.34/0.99      | ~ v3_pre_topc(sK6,sK3)
% 2.34/0.99      | ~ r2_hidden(sK7,sK6)
% 2.34/0.99      | ~ r1_tarski(sK6,sK6) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_7670]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_6522,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7719,plain,
% 2.34/0.99      ( k2_tmap_1(sK3,sK2,sK4,sK5) = k2_tmap_1(sK3,sK2,sK4,sK5) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_6522]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7588,plain,
% 2.34/0.99      ( r1_tmap_1(sK5,sK2,X0_54,X1_54)
% 2.34/0.99      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 2.34/0.99      | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.34/0.99      | X1_54 != sK8 ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_6529]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7662,plain,
% 2.34/0.99      ( r1_tmap_1(sK5,sK2,X0_54,sK7)
% 2.34/0.99      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 2.34/0.99      | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.34/0.99      | sK7 != sK8 ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_7588]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7718,plain,
% 2.34/0.99      ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.34/0.99      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 2.34/0.99      | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.34/0.99      | sK7 != sK8 ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_7662]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7713,plain,
% 2.34/0.99      ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_6522]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_6528,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0_54,X1_54)
% 2.34/0.99      | m1_subset_1(X2_54,X3_54)
% 2.34/0.99      | X2_54 != X0_54
% 2.34/0.99      | X3_54 != X1_54 ),
% 2.34/0.99      theory(equality) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7568,plain,
% 2.34/0.99      ( m1_subset_1(X0_54,X1_54)
% 2.34/0.99      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.34/0.99      | X1_54 != u1_struct_0(sK5)
% 2.34/0.99      | X0_54 != sK8 ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_6528]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7615,plain,
% 2.34/0.99      ( m1_subset_1(sK7,X0_54)
% 2.34/0.99      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.34/0.99      | X0_54 != u1_struct_0(sK5)
% 2.34/0.99      | sK7 != sK8 ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_7568]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7712,plain,
% 2.34/0.99      ( m1_subset_1(sK7,u1_struct_0(sK5))
% 2.34/0.99      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.34/0.99      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 2.34/0.99      | sK7 != sK8 ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_7615]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7621,plain,
% 2.34/0.99      ( sK8 = sK8 ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_6522]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_12,negated_conjecture,
% 2.34/0.99      ( sK7 = sK8 ),
% 2.34/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_6511,negated_conjecture,
% 2.34/0.99      ( sK7 = sK8 ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_10,negated_conjecture,
% 2.34/0.99      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.34/0.99      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 2.34/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_11,negated_conjecture,
% 2.34/0.99      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.34/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 2.34/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_13,negated_conjecture,
% 2.34/0.99      ( r1_tarski(sK6,u1_struct_0(sK5)) ),
% 2.34/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_14,negated_conjecture,
% 2.34/0.99      ( r2_hidden(sK7,sK6) ),
% 2.34/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_15,negated_conjecture,
% 2.34/0.99      ( v3_pre_topc(sK6,sK3) ),
% 2.34/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_16,negated_conjecture,
% 2.34/0.99      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 2.34/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_17,negated_conjecture,
% 2.34/0.99      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.34/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_18,negated_conjecture,
% 2.34/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.34/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(contradiction,plain,
% 2.34/0.99      ( $false ),
% 2.34/0.99      inference(minisat,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_9083,c_8410,c_8083,c_7933,c_7932,c_7865,c_7751,c_7719,
% 2.34/0.99                 c_7718,c_7713,c_7712,c_7621,c_6511,c_10,c_11,c_13,c_14,
% 2.34/0.99                 c_15,c_16,c_17,c_18]) ).
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.34/0.99  
% 2.34/0.99  ------                               Statistics
% 2.34/0.99  
% 2.34/0.99  ------ General
% 2.34/0.99  
% 2.34/0.99  abstr_ref_over_cycles:                  0
% 2.34/0.99  abstr_ref_under_cycles:                 0
% 2.34/0.99  gc_basic_clause_elim:                   0
% 2.34/0.99  forced_gc_time:                         0
% 2.34/0.99  parsing_time:                           0.008
% 2.34/0.99  unif_index_cands_time:                  0.
% 2.34/0.99  unif_index_add_time:                    0.
% 2.34/0.99  orderings_time:                         0.
% 2.34/0.99  out_proof_time:                         0.01
% 2.34/0.99  total_time:                             0.231
% 2.34/0.99  num_of_symbols:                         60
% 2.34/0.99  num_of_terms:                           3461
% 2.34/0.99  
% 2.34/0.99  ------ Preprocessing
% 2.34/0.99  
% 2.34/0.99  num_of_splits:                          2
% 2.34/0.99  num_of_split_atoms:                     2
% 2.34/0.99  num_of_reused_defs:                     0
% 2.34/0.99  num_eq_ax_congr_red:                    29
% 2.34/0.99  num_of_sem_filtered_clauses:            1
% 2.34/0.99  num_of_subtypes:                        2
% 2.34/0.99  monotx_restored_types:                  0
% 2.34/0.99  sat_num_of_epr_types:                   0
% 2.34/0.99  sat_num_of_non_cyclic_types:            0
% 2.34/0.99  sat_guarded_non_collapsed_types:        0
% 2.34/0.99  num_pure_diseq_elim:                    0
% 2.34/0.99  simp_replaced_by:                       0
% 2.34/0.99  res_preprocessed:                       136
% 2.34/0.99  prep_upred:                             0
% 2.34/0.99  prep_unflattend:                        238
% 2.34/0.99  smt_new_axioms:                         0
% 2.34/0.99  pred_elim_cands:                        6
% 2.34/0.99  pred_elim:                              6
% 2.34/0.99  pred_elim_cl:                           3
% 2.34/0.99  pred_elim_cycles:                       14
% 2.34/0.99  merged_defs:                            8
% 2.34/0.99  merged_defs_ncl:                        0
% 2.34/0.99  bin_hyper_res:                          8
% 2.34/0.99  prep_cycles:                            4
% 2.34/0.99  pred_elim_time:                         0.122
% 2.34/0.99  splitting_time:                         0.
% 2.34/0.99  sem_filter_time:                        0.
% 2.34/0.99  monotx_time:                            0.
% 2.34/0.99  subtype_inf_time:                       0.
% 2.34/0.99  
% 2.34/0.99  ------ Problem properties
% 2.34/0.99  
% 2.34/0.99  clauses:                                29
% 2.34/0.99  conjectures:                            10
% 2.34/0.99  epr:                                    4
% 2.34/0.99  horn:                                   27
% 2.34/0.99  ground:                                 12
% 2.34/0.99  unary:                                  8
% 2.34/0.99  binary:                                 4
% 2.34/0.99  lits:                                   101
% 2.34/0.99  lits_eq:                                3
% 2.34/0.99  fd_pure:                                0
% 2.34/0.99  fd_pseudo:                              0
% 2.34/0.99  fd_cond:                                0
% 2.34/0.99  fd_pseudo_cond:                         0
% 2.34/0.99  ac_symbols:                             0
% 2.34/0.99  
% 2.34/0.99  ------ Propositional Solver
% 2.34/0.99  
% 2.34/0.99  prop_solver_calls:                      28
% 2.34/0.99  prop_fast_solver_calls:                 2805
% 2.34/0.99  smt_solver_calls:                       0
% 2.34/0.99  smt_fast_solver_calls:                  0
% 2.34/0.99  prop_num_of_clauses:                    1278
% 2.34/0.99  prop_preprocess_simplified:             5164
% 2.34/0.99  prop_fo_subsumed:                       85
% 2.34/0.99  prop_solver_time:                       0.
% 2.34/0.99  smt_solver_time:                        0.
% 2.34/0.99  smt_fast_solver_time:                   0.
% 2.34/0.99  prop_fast_solver_time:                  0.
% 2.34/0.99  prop_unsat_core_time:                   0.
% 2.34/0.99  
% 2.34/0.99  ------ QBF
% 2.34/0.99  
% 2.34/0.99  qbf_q_res:                              0
% 2.34/0.99  qbf_num_tautologies:                    0
% 2.34/0.99  qbf_prep_cycles:                        0
% 2.34/0.99  
% 2.34/0.99  ------ BMC1
% 2.34/0.99  
% 2.34/0.99  bmc1_current_bound:                     -1
% 2.34/0.99  bmc1_last_solved_bound:                 -1
% 2.34/0.99  bmc1_unsat_core_size:                   -1
% 2.34/0.99  bmc1_unsat_core_parents_size:           -1
% 2.34/0.99  bmc1_merge_next_fun:                    0
% 2.34/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.34/0.99  
% 2.34/0.99  ------ Instantiation
% 2.34/0.99  
% 2.34/0.99  inst_num_of_clauses:                    242
% 2.34/0.99  inst_num_in_passive:                    19
% 2.34/0.99  inst_num_in_active:                     209
% 2.34/0.99  inst_num_in_unprocessed:                13
% 2.34/0.99  inst_num_of_loops:                      244
% 2.34/0.99  inst_num_of_learning_restarts:          0
% 2.34/0.99  inst_num_moves_active_passive:          29
% 2.34/0.99  inst_lit_activity:                      0
% 2.34/0.99  inst_lit_activity_moves:                0
% 2.34/0.99  inst_num_tautologies:                   0
% 2.34/0.99  inst_num_prop_implied:                  0
% 2.34/0.99  inst_num_existing_simplified:           0
% 2.34/0.99  inst_num_eq_res_simplified:             0
% 2.34/0.99  inst_num_child_elim:                    0
% 2.34/0.99  inst_num_of_dismatching_blockings:      21
% 2.34/0.99  inst_num_of_non_proper_insts:           267
% 2.34/0.99  inst_num_of_duplicates:                 0
% 2.34/0.99  inst_inst_num_from_inst_to_res:         0
% 2.34/0.99  inst_dismatching_checking_time:         0.
% 2.34/0.99  
% 2.34/0.99  ------ Resolution
% 2.34/0.99  
% 2.34/0.99  res_num_of_clauses:                     0
% 2.34/0.99  res_num_in_passive:                     0
% 2.34/0.99  res_num_in_active:                      0
% 2.34/0.99  res_num_of_loops:                       140
% 2.34/0.99  res_forward_subset_subsumed:            65
% 2.34/0.99  res_backward_subset_subsumed:           4
% 2.34/0.99  res_forward_subsumed:                   0
% 2.34/0.99  res_backward_subsumed:                  0
% 2.34/0.99  res_forward_subsumption_resolution:     4
% 2.34/0.99  res_backward_subsumption_resolution:    0
% 2.34/0.99  res_clause_to_clause_subsumption:       330
% 2.34/0.99  res_orphan_elimination:                 0
% 2.34/0.99  res_tautology_del:                      65
% 2.34/0.99  res_num_eq_res_simplified:              2
% 2.34/0.99  res_num_sel_changes:                    0
% 2.34/0.99  res_moves_from_active_to_pass:          0
% 2.34/0.99  
% 2.34/0.99  ------ Superposition
% 2.34/0.99  
% 2.34/0.99  sup_time_total:                         0.
% 2.34/0.99  sup_time_generating:                    0.
% 2.34/0.99  sup_time_sim_full:                      0.
% 2.34/0.99  sup_time_sim_immed:                     0.
% 2.34/0.99  
% 2.34/0.99  sup_num_of_clauses:                     63
% 2.34/0.99  sup_num_in_active:                      48
% 2.34/0.99  sup_num_in_passive:                     15
% 2.34/0.99  sup_num_of_loops:                       48
% 2.34/0.99  sup_fw_superposition:                   28
% 2.34/0.99  sup_bw_superposition:                   17
% 2.34/0.99  sup_immediate_simplified:               4
% 2.34/0.99  sup_given_eliminated:                   0
% 2.34/0.99  comparisons_done:                       0
% 2.34/0.99  comparisons_avoided:                    0
% 2.34/0.99  
% 2.34/0.99  ------ Simplifications
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  sim_fw_subset_subsumed:                 4
% 2.34/0.99  sim_bw_subset_subsumed:                 0
% 2.34/0.99  sim_fw_subsumed:                        0
% 2.34/0.99  sim_bw_subsumed:                        0
% 2.34/0.99  sim_fw_subsumption_res:                 0
% 2.34/0.99  sim_bw_subsumption_res:                 0
% 2.34/0.99  sim_tautology_del:                      2
% 2.34/0.99  sim_eq_tautology_del:                   0
% 2.34/0.99  sim_eq_res_simp:                        0
% 2.34/0.99  sim_fw_demodulated:                     0
% 2.34/0.99  sim_bw_demodulated:                     0
% 2.34/0.99  sim_light_normalised:                   4
% 2.34/0.99  sim_joinable_taut:                      0
% 2.34/0.99  sim_joinable_simp:                      0
% 2.34/0.99  sim_ac_normalised:                      0
% 2.34/0.99  sim_smt_subsumption:                    0
% 2.34/0.99  
%------------------------------------------------------------------------------
