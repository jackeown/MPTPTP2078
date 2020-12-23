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
% DateTime   : Thu Dec  3 12:23:13 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :  221 (2716 expanded)
%              Number of clauses        :  145 ( 587 expanded)
%              Number of leaves         :   18 (1119 expanded)
%              Depth                    :   33
%              Number of atoms          : 1819 (53603 expanded)
%              Number of equality atoms :  535 (3874 expanded)
%              Maximal formula depth    :   31 (   9 average)
%              Maximal clause size      :   50 (   7 average)
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
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X1) )
                                     => ( r1_tmap_1(X3,X0,X4,X6)
                                      <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X2))
                                     => ( ( X6 = X7
                                          & r1_tarski(X5,u1_struct_0(X2))
                                          & r2_hidden(X6,X5)
                                          & v3_pre_topc(X5,X1) )
                                       => ( r1_tmap_1(X3,X0,X4,X6)
                                        <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
            | ~ r1_tmap_1(X3,X0,X4,X6) )
          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
            | r1_tmap_1(X3,X0,X4,X6) )
          & X6 = X7
          & r1_tarski(X5,u1_struct_0(X2))
          & r2_hidden(X6,X5)
          & v3_pre_topc(X5,X1)
          & m1_subset_1(X7,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7)
          | ~ r1_tmap_1(X3,X0,X4,X6) )
        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7)
          | r1_tmap_1(X3,X0,X4,X6) )
        & sK7 = X6
        & r1_tarski(X5,u1_struct_0(X2))
        & r2_hidden(X6,X5)
        & v3_pre_topc(X5,X1)
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                | ~ r1_tmap_1(X3,X0,X4,X6) )
              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                | r1_tmap_1(X3,X0,X4,X6) )
              & X6 = X7
              & r1_tarski(X5,u1_struct_0(X2))
              & r2_hidden(X6,X5)
              & v3_pre_topc(X5,X1)
              & m1_subset_1(X7,u1_struct_0(X2)) )
          & m1_subset_1(X6,u1_struct_0(X3)) )
     => ( ? [X7] :
            ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
              | ~ r1_tmap_1(X3,X0,X4,sK6) )
            & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
              | r1_tmap_1(X3,X0,X4,sK6) )
            & sK6 = X7
            & r1_tarski(X5,u1_struct_0(X2))
            & r2_hidden(sK6,X5)
            & v3_pre_topc(X5,X1)
            & m1_subset_1(X7,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                    | r1_tmap_1(X3,X0,X4,X6) )
                  & X6 = X7
                  & r1_tarski(X5,u1_struct_0(X2))
                  & r2_hidden(X6,X5)
                  & v3_pre_topc(X5,X1)
                  & m1_subset_1(X7,u1_struct_0(X2)) )
              & m1_subset_1(X6,u1_struct_0(X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                  | ~ r1_tmap_1(X3,X0,X4,X6) )
                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                  | r1_tmap_1(X3,X0,X4,X6) )
                & X6 = X7
                & r1_tarski(sK5,u1_struct_0(X2))
                & r2_hidden(X6,sK5)
                & v3_pre_topc(sK5,X1)
                & m1_subset_1(X7,u1_struct_0(X2)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                        | ~ r1_tmap_1(X3,X0,X4,X6) )
                      & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                        | r1_tmap_1(X3,X0,X4,X6) )
                      & X6 = X7
                      & r1_tarski(X5,u1_struct_0(X2))
                      & r2_hidden(X6,X5)
                      & v3_pre_topc(X5,X1)
                      & m1_subset_1(X7,u1_struct_0(X2)) )
                  & m1_subset_1(X6,u1_struct_0(X3)) )
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7)
                      | ~ r1_tmap_1(X3,X0,sK4,X6) )
                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7)
                      | r1_tmap_1(X3,X0,sK4,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(X2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,X1)
                    & m1_subset_1(X7,u1_struct_0(X2)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                            | ~ r1_tmap_1(X3,X0,X4,X6) )
                          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                            | r1_tmap_1(X3,X0,X4,X6) )
                          & X6 = X7
                          & r1_tarski(X5,u1_struct_0(X2))
                          & r2_hidden(X6,X5)
                          & v3_pre_topc(X5,X1)
                          & m1_subset_1(X7,u1_struct_0(X2)) )
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X1)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7)
                          | ~ r1_tmap_1(sK3,X0,X4,X6) )
                        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7)
                          | r1_tmap_1(sK3,X0,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(X2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,X1)
                        & m1_subset_1(X7,u1_struct_0(X2)) )
                    & m1_subset_1(X6,u1_struct_0(sK3)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X2,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                | ~ r1_tmap_1(X3,X0,X4,X6) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                | r1_tmap_1(X3,X0,X4,X6) )
                              & X6 = X7
                              & r1_tarski(X5,u1_struct_0(X2))
                              & r2_hidden(X6,X5)
                              & v3_pre_topc(X5,X1)
                              & m1_subset_1(X7,u1_struct_0(X2)) )
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ( ~ r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7)
                              | ~ r1_tmap_1(X3,X0,X4,X6) )
                            & ( r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7)
                              | r1_tmap_1(X3,X0,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(sK2))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,X1)
                            & m1_subset_1(X7,u1_struct_0(sK2)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_pre_topc(sK2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X1)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
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
                                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,X0,X4,X6) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,X0,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,sK1)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X0,X4,X6) )
                                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | r1_tmap_1(X3,X0,X4,X6) )
                                    & X6 = X7
                                    & r1_tarski(X5,u1_struct_0(X2))
                                    & r2_hidden(X6,X5)
                                    & v3_pre_topc(X5,X1)
                                    & m1_subset_1(X7,u1_struct_0(X2)) )
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X1)
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
                                  ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,sK0,X4,X6) )
                                  & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,sK0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
      | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
      | r1_tmap_1(sK3,sK0,sK4,sK6) )
    & sK6 = sK7
    & r1_tarski(sK5,u1_struct_0(sK2))
    & r2_hidden(sK6,sK5)
    & v3_pre_topc(sK5,sK1)
    & m1_subset_1(sK7,u1_struct_0(sK2))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f32,f40,f39,f38,f37,f36,f35,f34,f33])).

fof(f68,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f45,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f78,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f7,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f41])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
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
    inference(equality_resolution,[],[f53])).

fof(f66,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f44,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f41])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
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
    inference(equality_resolution,[],[f54])).

fof(f77,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1601,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2420,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1601])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1602,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2419,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1602])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1614,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X1_53)))
    | ~ l1_pre_topc(X1_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2404,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X1_53))) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1614])).

cnf(c_3347,plain,
    ( m1_pre_topc(sK1,X0_53) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53))) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2419,c_2404])).

cnf(c_3871,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(sK1,X0_53) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1_53))) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_3347,c_2404])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1615,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1654,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1615])).

cnf(c_4489,plain,
    ( l1_pre_topc(X1_53) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1_53))) = iProver_top
    | m1_pre_topc(sK1,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3871,c_1654])).

cnf(c_4490,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(sK1,X0_53) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1_53))) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_4489])).

cnf(c_4497,plain,
    ( m1_pre_topc(sK1,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2420,c_4490])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_41,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_49,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_233,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_774,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | u1_struct_0(sK2) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_233,c_16])).

cnf(c_775,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_774])).

cnf(c_776,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_775])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1599,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_2422,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1599])).

cnf(c_2403,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1615])).

cnf(c_3261,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2422,c_2403])).

cnf(c_2768,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1614])).

cnf(c_3502,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2768])).

cnf(c_3503,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3502])).

cnf(c_4508,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4497,c_41,c_49,c_776,c_3261,c_3503])).

cnf(c_6,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1612,plain,
    ( ~ v3_pre_topc(X0_54,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X1_53)))
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X1_53)
    | k1_tops_1(X0_53,X0_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1623,plain,
    ( ~ v3_pre_topc(X0_54,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ l1_pre_topc(X0_53)
    | k1_tops_1(X0_53,X0_54) = X0_54
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_1612])).

cnf(c_2409,plain,
    ( k1_tops_1(X0_53,X0_54) = X0_54
    | v3_pre_topc(X0_54,X0_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1623])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_40,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_50,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1624,plain,
    ( sP3_iProver_split
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1612])).

cnf(c_1663,plain,
    ( sP3_iProver_split = iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1624])).

cnf(c_1664,plain,
    ( k1_tops_1(X0_53,X0_54) = X0_54
    | v3_pre_topc(X0_54,X0_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1623])).

cnf(c_1622,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X0_53)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_1612])).

cnf(c_3074,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ sP2_iProver_split ),
    inference(instantiation,[status(thm)],[c_1622])).

cnf(c_3075,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3074])).

cnf(c_4672,plain,
    ( l1_pre_topc(X0_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v3_pre_topc(X0_54,X0_53) != iProver_top
    | k1_tops_1(X0_53,X0_54) = X0_54 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2409,c_40,c_41,c_50,c_1663,c_1664,c_3075])).

cnf(c_4673,plain,
    ( k1_tops_1(X0_53,X0_54) = X0_54
    | v3_pre_topc(X0_54,X0_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_4672])).

cnf(c_4687,plain,
    ( k1_tops_1(sK3,sK5) = sK5
    | v3_pre_topc(sK5,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4508,c_4673])).

cnf(c_18,negated_conjecture,
    ( v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_7,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1611,plain,
    ( ~ v3_pre_topc(X0_54,X0_53)
    | v3_pre_topc(X0_54,X1_53)
    | ~ m1_pre_topc(X1_53,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X1_53)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2831,plain,
    ( v3_pre_topc(sK5,X0_53)
    | ~ v3_pre_topc(sK5,sK1)
    | ~ m1_pre_topc(X0_53,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1611])).

cnf(c_3102,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ v3_pre_topc(sK5,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2831])).

cnf(c_3276,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3261])).

cnf(c_2932,plain,
    ( ~ v3_pre_topc(sK5,X0_53)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ l1_pre_topc(X0_53)
    | ~ sP3_iProver_split
    | k1_tops_1(X0_53,sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_1623])).

cnf(c_3660,plain,
    ( ~ v3_pre_topc(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ sP3_iProver_split
    | k1_tops_1(sK3,sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_2932])).

cnf(c_5038,plain,
    ( k1_tops_1(sK3,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4687,c_31,c_30,c_26,c_22,c_21,c_18,c_775,c_1624,c_3074,c_3102,c_3276,c_3502,c_3660])).

cnf(c_8,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_442,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(X1,X0) != sK5
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_443,plain,
    ( m1_connsp_2(X0,X1,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK6,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(X1,X0) != sK5 ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_12,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
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
    inference(cnf_transformation,[],[f80])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_477,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
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
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_478,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_482,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_25])).

cnf(c_483,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
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
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_482])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_530,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
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
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_483,c_10])).

cnf(c_700,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X7))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X7)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X7)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X7)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | X5 != X6
    | X3 != X7
    | k1_tops_1(X7,X6) != sK5
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK6 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_443,c_530])).

cnf(c_701,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | ~ r1_tmap_1(X3,X1,sK4,sK6)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k1_tops_1(X3,X4) != sK5
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_700])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_749,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | ~ r1_tmap_1(X3,X1,sK4,sK6)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k1_tops_1(X3,X4) != sK5
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_701,c_2,c_3])).

cnf(c_1588,plain,
    ( r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),sK6)
    | ~ r1_tmap_1(X3_53,X1_53,sK4,sK6)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_pre_topc(X3_53,X2_53)
    | ~ r1_tarski(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X3_53)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK6,u1_struct_0(X3_53))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X3_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK0)
    | k1_tops_1(X3_53,X0_54) != sK5 ),
    inference(subtyping,[status(esa)],[c_749])).

cnf(c_2433,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK0)
    | k1_tops_1(X0_53,X0_54) != sK5
    | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4),sK6) = iProver_top
    | r1_tmap_1(X0_53,X1_53,sK4,sK6) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X2_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X2_53)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1588])).

cnf(c_15,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1607,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2618,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK0)
    | k1_tops_1(X0_53,X0_54) != sK5
    | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4),sK7) = iProver_top
    | r1_tmap_1(X0_53,X1_53,sK4,sK7) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X2_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X2_53)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2433,c_1607])).

cnf(c_3498,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | k1_tops_1(X0_53,X0_54) != sK5
    | r1_tmap_1(X1_53,sK0,k3_tmap_1(X2_53,sK0,X0_53,X1_53,sK4),sK7) = iProver_top
    | r1_tmap_1(X0_53,sK0,sK4,sK7) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2618])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_36,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_37,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_38,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4104,plain,
    ( v2_pre_topc(X2_53) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | r1_tmap_1(X0_53,sK0,sK4,sK7) != iProver_top
    | r1_tmap_1(X1_53,sK0,k3_tmap_1(X2_53,sK0,X0_53,X1_53,sK4),sK7) = iProver_top
    | k1_tops_1(X0_53,X0_54) != sK5
    | u1_struct_0(X0_53) != u1_struct_0(sK3)
    | l1_pre_topc(X2_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3498,c_36,c_37,c_38])).

cnf(c_4105,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | k1_tops_1(X0_53,X0_54) != sK5
    | r1_tmap_1(X1_53,sK0,k3_tmap_1(X2_53,sK0,X0_53,X1_53,sK4),sK7) = iProver_top
    | r1_tmap_1(X0_53,sK0,sK4,sK7) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_4104])).

cnf(c_4124,plain,
    ( k1_tops_1(sK3,X0_54) != sK5
    | r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) = iProver_top
    | r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4105])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_44,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_48,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1603,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2418,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1603])).

cnf(c_2464,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2418,c_1607])).

cnf(c_5258,plain,
    ( v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
    | r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) = iProver_top
    | k1_tops_1(sK3,X0_54) != sK5
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4124,c_44,c_48,c_2464])).

cnf(c_5259,plain,
    ( k1_tops_1(sK3,X0_54) != sK5
    | r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) = iProver_top
    | r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5258])).

cnf(c_5276,plain,
    ( r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) = iProver_top
    | r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_5038,c_5259])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_39,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_42,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_45,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_52,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_55,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1608,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2414,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1608])).

cnf(c_2499,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2414,c_1607])).

cnf(c_11,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
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
    inference(cnf_transformation,[],[f79])).

cnf(c_552,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
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
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_553,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_557,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_connsp_2(X5,X3,X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_25])).

cnf(c_558,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
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
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_557])).

cnf(c_605,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
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
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_558,c_10])).

cnf(c_629,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X7))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X7)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X7)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X7)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | X5 != X6
    | X3 != X7
    | k1_tops_1(X7,X6) != sK5
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK6 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_443,c_605])).

cnf(c_630,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | r1_tmap_1(X3,X1,sK4,sK6)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k1_tops_1(X3,X4) != sK5
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_678,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | r1_tmap_1(X3,X1,sK4,sK6)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k1_tops_1(X3,X4) != sK5
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_630,c_2,c_3])).

cnf(c_1589,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),sK6)
    | r1_tmap_1(X3_53,X1_53,sK4,sK6)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_pre_topc(X3_53,X2_53)
    | ~ r1_tarski(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X3_53)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK6,u1_struct_0(X3_53))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X3_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK0)
    | k1_tops_1(X3_53,X0_54) != sK5 ),
    inference(subtyping,[status(esa)],[c_678])).

cnf(c_2432,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK0)
    | k1_tops_1(X0_53,X0_54) != sK5
    | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4),sK6) != iProver_top
    | r1_tmap_1(X0_53,X1_53,sK4,sK6) = iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X2_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X2_53)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1589])).

cnf(c_2577,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK0)
    | k1_tops_1(X0_53,X0_54) != sK5
    | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4),sK7) != iProver_top
    | r1_tmap_1(X0_53,X1_53,sK4,sK7) = iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X2_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X2_53)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2432,c_1607])).

cnf(c_3473,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | k1_tops_1(X0_53,X0_54) != sK5
    | r1_tmap_1(X1_53,sK0,k3_tmap_1(X2_53,sK0,X0_53,X1_53,sK4),sK7) != iProver_top
    | r1_tmap_1(X0_53,sK0,sK4,sK7) = iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2577])).

cnf(c_4032,plain,
    ( v2_pre_topc(X2_53) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | r1_tmap_1(X0_53,sK0,sK4,sK7) = iProver_top
    | r1_tmap_1(X1_53,sK0,k3_tmap_1(X2_53,sK0,X0_53,X1_53,sK4),sK7) != iProver_top
    | k1_tops_1(X0_53,X0_54) != sK5
    | u1_struct_0(X0_53) != u1_struct_0(sK3)
    | l1_pre_topc(X2_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3473,c_36,c_37,c_38])).

cnf(c_4033,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | k1_tops_1(X0_53,X0_54) != sK5
    | r1_tmap_1(X1_53,sK0,k3_tmap_1(X2_53,sK0,X0_53,X1_53,sK4),sK7) != iProver_top
    | r1_tmap_1(X0_53,sK0,sK4,sK7) = iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_4032])).

cnf(c_4052,plain,
    ( k1_tops_1(sK3,X0_54) != sK5
    | r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) != iProver_top
    | r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4033])).

cnf(c_5235,plain,
    ( v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
    | r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) != iProver_top
    | k1_tops_1(sK3,X0_54) != sK5
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4052,c_44,c_48,c_2464])).

cnf(c_5236,plain,
    ( k1_tops_1(sK3,X0_54) != sK5
    | r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) != iProver_top
    | r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5235])).

cnf(c_5253,plain,
    ( r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) != iProver_top
    | r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_5038,c_5236])).

cnf(c_5841,plain,
    ( r1_tarski(sK5,u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
    | r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5253,c_41,c_49,c_776,c_3261,c_3503])).

cnf(c_5842,plain,
    ( r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) != iProver_top
    | r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5841])).

cnf(c_5857,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2499,c_5842])).

cnf(c_5929,plain,
    ( r1_tarski(sK5,u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5276,c_39,c_40,c_41,c_42,c_45,c_49,c_52,c_55,c_776,c_3261,c_3503,c_5857])).

cnf(c_5930,plain,
    ( r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) = iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5929])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1609,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2413,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1609])).

cnf(c_2504,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2413,c_1607])).

cnf(c_5944,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5930,c_2504])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5944,c_5857,c_55,c_52,c_49,c_45,c_42,c_41,c_40,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.49/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.06  
% 2.49/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.49/1.06  
% 2.49/1.06  ------  iProver source info
% 2.49/1.06  
% 2.49/1.06  git: date: 2020-06-30 10:37:57 +0100
% 2.49/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.49/1.06  git: non_committed_changes: false
% 2.49/1.06  git: last_make_outside_of_git: false
% 2.49/1.06  
% 2.49/1.06  ------ 
% 2.49/1.06  
% 2.49/1.06  ------ Input Options
% 2.49/1.06  
% 2.49/1.06  --out_options                           all
% 2.49/1.06  --tptp_safe_out                         true
% 2.49/1.06  --problem_path                          ""
% 2.49/1.06  --include_path                          ""
% 2.49/1.06  --clausifier                            res/vclausify_rel
% 2.49/1.06  --clausifier_options                    --mode clausify
% 2.49/1.06  --stdin                                 false
% 2.49/1.06  --stats_out                             all
% 2.49/1.06  
% 2.49/1.06  ------ General Options
% 2.49/1.06  
% 2.49/1.06  --fof                                   false
% 2.49/1.06  --time_out_real                         305.
% 2.49/1.06  --time_out_virtual                      -1.
% 2.49/1.06  --symbol_type_check                     false
% 2.49/1.06  --clausify_out                          false
% 2.49/1.06  --sig_cnt_out                           false
% 2.49/1.06  --trig_cnt_out                          false
% 2.49/1.06  --trig_cnt_out_tolerance                1.
% 2.49/1.06  --trig_cnt_out_sk_spl                   false
% 2.49/1.06  --abstr_cl_out                          false
% 2.49/1.06  
% 2.49/1.06  ------ Global Options
% 2.49/1.06  
% 2.49/1.06  --schedule                              default
% 2.49/1.06  --add_important_lit                     false
% 2.49/1.06  --prop_solver_per_cl                    1000
% 2.49/1.06  --min_unsat_core                        false
% 2.49/1.06  --soft_assumptions                      false
% 2.49/1.06  --soft_lemma_size                       3
% 2.49/1.06  --prop_impl_unit_size                   0
% 2.49/1.06  --prop_impl_unit                        []
% 2.49/1.06  --share_sel_clauses                     true
% 2.49/1.06  --reset_solvers                         false
% 2.49/1.06  --bc_imp_inh                            [conj_cone]
% 2.49/1.06  --conj_cone_tolerance                   3.
% 2.49/1.06  --extra_neg_conj                        none
% 2.49/1.06  --large_theory_mode                     true
% 2.49/1.06  --prolific_symb_bound                   200
% 2.49/1.06  --lt_threshold                          2000
% 2.49/1.06  --clause_weak_htbl                      true
% 2.49/1.06  --gc_record_bc_elim                     false
% 2.49/1.06  
% 2.49/1.06  ------ Preprocessing Options
% 2.49/1.06  
% 2.49/1.06  --preprocessing_flag                    true
% 2.49/1.06  --time_out_prep_mult                    0.1
% 2.49/1.06  --splitting_mode                        input
% 2.49/1.06  --splitting_grd                         true
% 2.49/1.06  --splitting_cvd                         false
% 2.49/1.06  --splitting_cvd_svl                     false
% 2.49/1.06  --splitting_nvd                         32
% 2.49/1.06  --sub_typing                            true
% 2.49/1.06  --prep_gs_sim                           true
% 2.49/1.06  --prep_unflatten                        true
% 2.49/1.06  --prep_res_sim                          true
% 2.49/1.06  --prep_upred                            true
% 2.49/1.06  --prep_sem_filter                       exhaustive
% 2.49/1.06  --prep_sem_filter_out                   false
% 2.49/1.06  --pred_elim                             true
% 2.49/1.06  --res_sim_input                         true
% 2.49/1.06  --eq_ax_congr_red                       true
% 2.49/1.06  --pure_diseq_elim                       true
% 2.49/1.06  --brand_transform                       false
% 2.49/1.06  --non_eq_to_eq                          false
% 2.49/1.06  --prep_def_merge                        true
% 2.49/1.06  --prep_def_merge_prop_impl              false
% 2.49/1.06  --prep_def_merge_mbd                    true
% 2.49/1.06  --prep_def_merge_tr_red                 false
% 2.49/1.06  --prep_def_merge_tr_cl                  false
% 2.49/1.06  --smt_preprocessing                     true
% 2.49/1.06  --smt_ac_axioms                         fast
% 2.49/1.06  --preprocessed_out                      false
% 2.49/1.06  --preprocessed_stats                    false
% 2.49/1.06  
% 2.49/1.06  ------ Abstraction refinement Options
% 2.49/1.06  
% 2.49/1.06  --abstr_ref                             []
% 2.49/1.06  --abstr_ref_prep                        false
% 2.49/1.06  --abstr_ref_until_sat                   false
% 2.49/1.06  --abstr_ref_sig_restrict                funpre
% 2.49/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/1.06  --abstr_ref_under                       []
% 2.49/1.06  
% 2.49/1.06  ------ SAT Options
% 2.49/1.06  
% 2.49/1.06  --sat_mode                              false
% 2.49/1.06  --sat_fm_restart_options                ""
% 2.49/1.06  --sat_gr_def                            false
% 2.49/1.06  --sat_epr_types                         true
% 2.49/1.06  --sat_non_cyclic_types                  false
% 2.49/1.06  --sat_finite_models                     false
% 2.49/1.06  --sat_fm_lemmas                         false
% 2.49/1.06  --sat_fm_prep                           false
% 2.49/1.06  --sat_fm_uc_incr                        true
% 2.49/1.06  --sat_out_model                         small
% 2.49/1.06  --sat_out_clauses                       false
% 2.49/1.06  
% 2.49/1.06  ------ QBF Options
% 2.49/1.06  
% 2.49/1.06  --qbf_mode                              false
% 2.49/1.06  --qbf_elim_univ                         false
% 2.49/1.06  --qbf_dom_inst                          none
% 2.49/1.06  --qbf_dom_pre_inst                      false
% 2.49/1.06  --qbf_sk_in                             false
% 2.49/1.06  --qbf_pred_elim                         true
% 2.49/1.06  --qbf_split                             512
% 2.49/1.06  
% 2.49/1.06  ------ BMC1 Options
% 2.49/1.06  
% 2.49/1.06  --bmc1_incremental                      false
% 2.49/1.06  --bmc1_axioms                           reachable_all
% 2.49/1.06  --bmc1_min_bound                        0
% 2.49/1.06  --bmc1_max_bound                        -1
% 2.49/1.06  --bmc1_max_bound_default                -1
% 2.49/1.06  --bmc1_symbol_reachability              true
% 2.49/1.06  --bmc1_property_lemmas                  false
% 2.49/1.06  --bmc1_k_induction                      false
% 2.49/1.06  --bmc1_non_equiv_states                 false
% 2.49/1.06  --bmc1_deadlock                         false
% 2.49/1.06  --bmc1_ucm                              false
% 2.49/1.06  --bmc1_add_unsat_core                   none
% 2.49/1.06  --bmc1_unsat_core_children              false
% 2.49/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/1.06  --bmc1_out_stat                         full
% 2.49/1.06  --bmc1_ground_init                      false
% 2.49/1.06  --bmc1_pre_inst_next_state              false
% 2.49/1.06  --bmc1_pre_inst_state                   false
% 2.49/1.06  --bmc1_pre_inst_reach_state             false
% 2.49/1.06  --bmc1_out_unsat_core                   false
% 2.49/1.06  --bmc1_aig_witness_out                  false
% 2.49/1.06  --bmc1_verbose                          false
% 2.49/1.06  --bmc1_dump_clauses_tptp                false
% 2.49/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.49/1.06  --bmc1_dump_file                        -
% 2.49/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.49/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.49/1.06  --bmc1_ucm_extend_mode                  1
% 2.49/1.06  --bmc1_ucm_init_mode                    2
% 2.49/1.06  --bmc1_ucm_cone_mode                    none
% 2.49/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.49/1.06  --bmc1_ucm_relax_model                  4
% 2.49/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.49/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/1.06  --bmc1_ucm_layered_model                none
% 2.49/1.06  --bmc1_ucm_max_lemma_size               10
% 2.49/1.06  
% 2.49/1.06  ------ AIG Options
% 2.49/1.06  
% 2.49/1.06  --aig_mode                              false
% 2.49/1.06  
% 2.49/1.06  ------ Instantiation Options
% 2.49/1.06  
% 2.49/1.06  --instantiation_flag                    true
% 2.49/1.06  --inst_sos_flag                         false
% 2.49/1.06  --inst_sos_phase                        true
% 2.49/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/1.06  --inst_lit_sel_side                     num_symb
% 2.49/1.06  --inst_solver_per_active                1400
% 2.49/1.06  --inst_solver_calls_frac                1.
% 2.49/1.06  --inst_passive_queue_type               priority_queues
% 2.49/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/1.06  --inst_passive_queues_freq              [25;2]
% 2.49/1.06  --inst_dismatching                      true
% 2.49/1.06  --inst_eager_unprocessed_to_passive     true
% 2.49/1.06  --inst_prop_sim_given                   true
% 2.49/1.06  --inst_prop_sim_new                     false
% 2.49/1.06  --inst_subs_new                         false
% 2.49/1.06  --inst_eq_res_simp                      false
% 2.49/1.06  --inst_subs_given                       false
% 2.49/1.06  --inst_orphan_elimination               true
% 2.49/1.06  --inst_learning_loop_flag               true
% 2.49/1.06  --inst_learning_start                   3000
% 2.49/1.06  --inst_learning_factor                  2
% 2.49/1.06  --inst_start_prop_sim_after_learn       3
% 2.49/1.06  --inst_sel_renew                        solver
% 2.49/1.06  --inst_lit_activity_flag                true
% 2.49/1.06  --inst_restr_to_given                   false
% 2.49/1.06  --inst_activity_threshold               500
% 2.49/1.06  --inst_out_proof                        true
% 2.49/1.06  
% 2.49/1.06  ------ Resolution Options
% 2.49/1.06  
% 2.49/1.06  --resolution_flag                       true
% 2.49/1.06  --res_lit_sel                           adaptive
% 2.49/1.06  --res_lit_sel_side                      none
% 2.49/1.06  --res_ordering                          kbo
% 2.49/1.06  --res_to_prop_solver                    active
% 2.49/1.06  --res_prop_simpl_new                    false
% 2.49/1.06  --res_prop_simpl_given                  true
% 2.49/1.06  --res_passive_queue_type                priority_queues
% 2.49/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/1.06  --res_passive_queues_freq               [15;5]
% 2.49/1.06  --res_forward_subs                      full
% 2.49/1.06  --res_backward_subs                     full
% 2.49/1.06  --res_forward_subs_resolution           true
% 2.49/1.06  --res_backward_subs_resolution          true
% 2.49/1.06  --res_orphan_elimination                true
% 2.49/1.06  --res_time_limit                        2.
% 2.49/1.06  --res_out_proof                         true
% 2.49/1.06  
% 2.49/1.06  ------ Superposition Options
% 2.49/1.06  
% 2.49/1.06  --superposition_flag                    true
% 2.49/1.06  --sup_passive_queue_type                priority_queues
% 2.49/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.49/1.06  --demod_completeness_check              fast
% 2.49/1.06  --demod_use_ground                      true
% 2.49/1.06  --sup_to_prop_solver                    passive
% 2.49/1.06  --sup_prop_simpl_new                    true
% 2.49/1.06  --sup_prop_simpl_given                  true
% 2.49/1.06  --sup_fun_splitting                     false
% 2.49/1.06  --sup_smt_interval                      50000
% 2.49/1.06  
% 2.49/1.06  ------ Superposition Simplification Setup
% 2.49/1.06  
% 2.49/1.06  --sup_indices_passive                   []
% 2.49/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.06  --sup_full_bw                           [BwDemod]
% 2.49/1.06  --sup_immed_triv                        [TrivRules]
% 2.49/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.06  --sup_immed_bw_main                     []
% 2.49/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.06  
% 2.49/1.06  ------ Combination Options
% 2.49/1.06  
% 2.49/1.06  --comb_res_mult                         3
% 2.49/1.06  --comb_sup_mult                         2
% 2.49/1.06  --comb_inst_mult                        10
% 2.49/1.06  
% 2.49/1.06  ------ Debug Options
% 2.49/1.06  
% 2.49/1.06  --dbg_backtrace                         false
% 2.49/1.06  --dbg_dump_prop_clauses                 false
% 2.49/1.06  --dbg_dump_prop_clauses_file            -
% 2.49/1.06  --dbg_out_stat                          false
% 2.49/1.06  ------ Parsing...
% 2.49/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.49/1.06  
% 2.49/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.49/1.06  
% 2.49/1.06  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.49/1.06  
% 2.49/1.06  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.49/1.06  ------ Proving...
% 2.49/1.06  ------ Problem Properties 
% 2.49/1.06  
% 2.49/1.06  
% 2.49/1.06  clauses                                 35
% 2.49/1.06  conjectures                             20
% 2.49/1.06  EPR                                     18
% 2.49/1.06  Horn                                    30
% 2.49/1.06  unary                                   18
% 2.49/1.06  binary                                  6
% 2.49/1.06  lits                                    110
% 2.49/1.06  lits eq                                 9
% 2.49/1.06  fd_pure                                 0
% 2.49/1.06  fd_pseudo                               0
% 2.49/1.06  fd_cond                                 0
% 2.49/1.06  fd_pseudo_cond                          0
% 2.49/1.06  AC symbols                              0
% 2.49/1.06  
% 2.49/1.06  ------ Schedule dynamic 5 is on 
% 2.49/1.06  
% 2.49/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.49/1.06  
% 2.49/1.06  
% 2.49/1.06  ------ 
% 2.49/1.06  Current options:
% 2.49/1.06  ------ 
% 2.49/1.06  
% 2.49/1.06  ------ Input Options
% 2.49/1.06  
% 2.49/1.06  --out_options                           all
% 2.49/1.06  --tptp_safe_out                         true
% 2.49/1.06  --problem_path                          ""
% 2.49/1.06  --include_path                          ""
% 2.49/1.06  --clausifier                            res/vclausify_rel
% 2.49/1.06  --clausifier_options                    --mode clausify
% 2.49/1.06  --stdin                                 false
% 2.49/1.06  --stats_out                             all
% 2.49/1.06  
% 2.49/1.06  ------ General Options
% 2.49/1.06  
% 2.49/1.06  --fof                                   false
% 2.49/1.06  --time_out_real                         305.
% 2.49/1.06  --time_out_virtual                      -1.
% 2.49/1.06  --symbol_type_check                     false
% 2.49/1.06  --clausify_out                          false
% 2.49/1.06  --sig_cnt_out                           false
% 2.49/1.06  --trig_cnt_out                          false
% 2.49/1.06  --trig_cnt_out_tolerance                1.
% 2.49/1.06  --trig_cnt_out_sk_spl                   false
% 2.49/1.06  --abstr_cl_out                          false
% 2.49/1.06  
% 2.49/1.06  ------ Global Options
% 2.49/1.06  
% 2.49/1.06  --schedule                              default
% 2.49/1.06  --add_important_lit                     false
% 2.49/1.06  --prop_solver_per_cl                    1000
% 2.49/1.06  --min_unsat_core                        false
% 2.49/1.06  --soft_assumptions                      false
% 2.49/1.06  --soft_lemma_size                       3
% 2.49/1.06  --prop_impl_unit_size                   0
% 2.49/1.06  --prop_impl_unit                        []
% 2.49/1.06  --share_sel_clauses                     true
% 2.49/1.06  --reset_solvers                         false
% 2.49/1.06  --bc_imp_inh                            [conj_cone]
% 2.49/1.06  --conj_cone_tolerance                   3.
% 2.49/1.06  --extra_neg_conj                        none
% 2.49/1.06  --large_theory_mode                     true
% 2.49/1.06  --prolific_symb_bound                   200
% 2.49/1.06  --lt_threshold                          2000
% 2.49/1.06  --clause_weak_htbl                      true
% 2.49/1.06  --gc_record_bc_elim                     false
% 2.49/1.06  
% 2.49/1.06  ------ Preprocessing Options
% 2.49/1.06  
% 2.49/1.06  --preprocessing_flag                    true
% 2.49/1.06  --time_out_prep_mult                    0.1
% 2.49/1.06  --splitting_mode                        input
% 2.49/1.06  --splitting_grd                         true
% 2.49/1.06  --splitting_cvd                         false
% 2.49/1.06  --splitting_cvd_svl                     false
% 2.49/1.06  --splitting_nvd                         32
% 2.49/1.06  --sub_typing                            true
% 2.49/1.06  --prep_gs_sim                           true
% 2.49/1.06  --prep_unflatten                        true
% 2.49/1.06  --prep_res_sim                          true
% 2.49/1.06  --prep_upred                            true
% 2.49/1.06  --prep_sem_filter                       exhaustive
% 2.49/1.06  --prep_sem_filter_out                   false
% 2.49/1.06  --pred_elim                             true
% 2.49/1.06  --res_sim_input                         true
% 2.49/1.06  --eq_ax_congr_red                       true
% 2.49/1.06  --pure_diseq_elim                       true
% 2.49/1.06  --brand_transform                       false
% 2.49/1.06  --non_eq_to_eq                          false
% 2.49/1.06  --prep_def_merge                        true
% 2.49/1.06  --prep_def_merge_prop_impl              false
% 2.49/1.06  --prep_def_merge_mbd                    true
% 2.49/1.06  --prep_def_merge_tr_red                 false
% 2.49/1.06  --prep_def_merge_tr_cl                  false
% 2.49/1.06  --smt_preprocessing                     true
% 2.49/1.06  --smt_ac_axioms                         fast
% 2.49/1.06  --preprocessed_out                      false
% 2.49/1.06  --preprocessed_stats                    false
% 2.49/1.06  
% 2.49/1.06  ------ Abstraction refinement Options
% 2.49/1.06  
% 2.49/1.06  --abstr_ref                             []
% 2.49/1.06  --abstr_ref_prep                        false
% 2.49/1.06  --abstr_ref_until_sat                   false
% 2.49/1.06  --abstr_ref_sig_restrict                funpre
% 2.49/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/1.06  --abstr_ref_under                       []
% 2.49/1.06  
% 2.49/1.06  ------ SAT Options
% 2.49/1.06  
% 2.49/1.06  --sat_mode                              false
% 2.49/1.06  --sat_fm_restart_options                ""
% 2.49/1.06  --sat_gr_def                            false
% 2.49/1.06  --sat_epr_types                         true
% 2.49/1.06  --sat_non_cyclic_types                  false
% 2.49/1.06  --sat_finite_models                     false
% 2.49/1.06  --sat_fm_lemmas                         false
% 2.49/1.06  --sat_fm_prep                           false
% 2.49/1.06  --sat_fm_uc_incr                        true
% 2.49/1.06  --sat_out_model                         small
% 2.49/1.06  --sat_out_clauses                       false
% 2.49/1.06  
% 2.49/1.06  ------ QBF Options
% 2.49/1.06  
% 2.49/1.06  --qbf_mode                              false
% 2.49/1.06  --qbf_elim_univ                         false
% 2.49/1.06  --qbf_dom_inst                          none
% 2.49/1.06  --qbf_dom_pre_inst                      false
% 2.49/1.06  --qbf_sk_in                             false
% 2.49/1.06  --qbf_pred_elim                         true
% 2.49/1.06  --qbf_split                             512
% 2.49/1.06  
% 2.49/1.06  ------ BMC1 Options
% 2.49/1.06  
% 2.49/1.06  --bmc1_incremental                      false
% 2.49/1.06  --bmc1_axioms                           reachable_all
% 2.49/1.06  --bmc1_min_bound                        0
% 2.49/1.06  --bmc1_max_bound                        -1
% 2.49/1.06  --bmc1_max_bound_default                -1
% 2.49/1.06  --bmc1_symbol_reachability              true
% 2.49/1.06  --bmc1_property_lemmas                  false
% 2.49/1.06  --bmc1_k_induction                      false
% 2.49/1.06  --bmc1_non_equiv_states                 false
% 2.49/1.06  --bmc1_deadlock                         false
% 2.49/1.06  --bmc1_ucm                              false
% 2.49/1.06  --bmc1_add_unsat_core                   none
% 2.49/1.06  --bmc1_unsat_core_children              false
% 2.49/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/1.06  --bmc1_out_stat                         full
% 2.49/1.06  --bmc1_ground_init                      false
% 2.49/1.06  --bmc1_pre_inst_next_state              false
% 2.49/1.06  --bmc1_pre_inst_state                   false
% 2.49/1.06  --bmc1_pre_inst_reach_state             false
% 2.49/1.06  --bmc1_out_unsat_core                   false
% 2.49/1.06  --bmc1_aig_witness_out                  false
% 2.49/1.06  --bmc1_verbose                          false
% 2.49/1.06  --bmc1_dump_clauses_tptp                false
% 2.49/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.49/1.06  --bmc1_dump_file                        -
% 2.49/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.49/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.49/1.06  --bmc1_ucm_extend_mode                  1
% 2.49/1.06  --bmc1_ucm_init_mode                    2
% 2.49/1.06  --bmc1_ucm_cone_mode                    none
% 2.49/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.49/1.06  --bmc1_ucm_relax_model                  4
% 2.49/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.49/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/1.06  --bmc1_ucm_layered_model                none
% 2.49/1.06  --bmc1_ucm_max_lemma_size               10
% 2.49/1.06  
% 2.49/1.06  ------ AIG Options
% 2.49/1.06  
% 2.49/1.06  --aig_mode                              false
% 2.49/1.06  
% 2.49/1.06  ------ Instantiation Options
% 2.49/1.06  
% 2.49/1.06  --instantiation_flag                    true
% 2.49/1.06  --inst_sos_flag                         false
% 2.49/1.06  --inst_sos_phase                        true
% 2.49/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/1.06  --inst_lit_sel_side                     none
% 2.49/1.06  --inst_solver_per_active                1400
% 2.49/1.06  --inst_solver_calls_frac                1.
% 2.49/1.06  --inst_passive_queue_type               priority_queues
% 2.49/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/1.06  --inst_passive_queues_freq              [25;2]
% 2.49/1.06  --inst_dismatching                      true
% 2.49/1.06  --inst_eager_unprocessed_to_passive     true
% 2.49/1.06  --inst_prop_sim_given                   true
% 2.49/1.06  --inst_prop_sim_new                     false
% 2.49/1.06  --inst_subs_new                         false
% 2.49/1.06  --inst_eq_res_simp                      false
% 2.49/1.06  --inst_subs_given                       false
% 2.49/1.06  --inst_orphan_elimination               true
% 2.49/1.06  --inst_learning_loop_flag               true
% 2.49/1.06  --inst_learning_start                   3000
% 2.49/1.06  --inst_learning_factor                  2
% 2.49/1.06  --inst_start_prop_sim_after_learn       3
% 2.49/1.06  --inst_sel_renew                        solver
% 2.49/1.06  --inst_lit_activity_flag                true
% 2.49/1.06  --inst_restr_to_given                   false
% 2.49/1.06  --inst_activity_threshold               500
% 2.49/1.06  --inst_out_proof                        true
% 2.49/1.06  
% 2.49/1.06  ------ Resolution Options
% 2.49/1.06  
% 2.49/1.06  --resolution_flag                       false
% 2.49/1.06  --res_lit_sel                           adaptive
% 2.49/1.06  --res_lit_sel_side                      none
% 2.49/1.06  --res_ordering                          kbo
% 2.49/1.06  --res_to_prop_solver                    active
% 2.49/1.06  --res_prop_simpl_new                    false
% 2.49/1.06  --res_prop_simpl_given                  true
% 2.49/1.06  --res_passive_queue_type                priority_queues
% 2.49/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/1.06  --res_passive_queues_freq               [15;5]
% 2.49/1.06  --res_forward_subs                      full
% 2.49/1.06  --res_backward_subs                     full
% 2.49/1.06  --res_forward_subs_resolution           true
% 2.49/1.06  --res_backward_subs_resolution          true
% 2.49/1.06  --res_orphan_elimination                true
% 2.49/1.06  --res_time_limit                        2.
% 2.49/1.06  --res_out_proof                         true
% 2.49/1.06  
% 2.49/1.06  ------ Superposition Options
% 2.49/1.06  
% 2.49/1.06  --superposition_flag                    true
% 2.49/1.06  --sup_passive_queue_type                priority_queues
% 2.49/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.49/1.06  --demod_completeness_check              fast
% 2.49/1.06  --demod_use_ground                      true
% 2.49/1.06  --sup_to_prop_solver                    passive
% 2.49/1.06  --sup_prop_simpl_new                    true
% 2.49/1.06  --sup_prop_simpl_given                  true
% 2.49/1.06  --sup_fun_splitting                     false
% 2.49/1.06  --sup_smt_interval                      50000
% 2.49/1.06  
% 2.49/1.06  ------ Superposition Simplification Setup
% 2.49/1.06  
% 2.49/1.06  --sup_indices_passive                   []
% 2.49/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.06  --sup_full_bw                           [BwDemod]
% 2.49/1.06  --sup_immed_triv                        [TrivRules]
% 2.49/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.06  --sup_immed_bw_main                     []
% 2.49/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.06  
% 2.49/1.06  ------ Combination Options
% 2.49/1.06  
% 2.49/1.06  --comb_res_mult                         3
% 2.49/1.06  --comb_sup_mult                         2
% 2.49/1.06  --comb_inst_mult                        10
% 2.49/1.06  
% 2.49/1.06  ------ Debug Options
% 2.49/1.06  
% 2.49/1.06  --dbg_backtrace                         false
% 2.49/1.06  --dbg_dump_prop_clauses                 false
% 2.49/1.06  --dbg_dump_prop_clauses_file            -
% 2.49/1.06  --dbg_out_stat                          false
% 2.49/1.06  
% 2.49/1.06  
% 2.49/1.06  
% 2.49/1.06  
% 2.49/1.06  ------ Proving...
% 2.49/1.06  
% 2.49/1.06  
% 2.49/1.06  % SZS status Theorem for theBenchmark.p
% 2.49/1.06  
% 2.49/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 2.49/1.06  
% 2.49/1.06  fof(f10,conjecture,(
% 2.49/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 2.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.06  
% 2.49/1.06  fof(f11,negated_conjecture,(
% 2.49/1.06    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 2.49/1.06    inference(negated_conjecture,[],[f10])).
% 2.49/1.06  
% 2.49/1.06  fof(f26,plain,(
% 2.49/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.49/1.06    inference(ennf_transformation,[],[f11])).
% 2.49/1.06  
% 2.49/1.06  fof(f27,plain,(
% 2.49/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.49/1.06    inference(flattening,[],[f26])).
% 2.49/1.06  
% 2.49/1.06  fof(f31,plain,(
% 2.49/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.49/1.06    inference(nnf_transformation,[],[f27])).
% 2.49/1.06  
% 2.49/1.06  fof(f32,plain,(
% 2.49/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.49/1.06    inference(flattening,[],[f31])).
% 2.49/1.06  
% 2.49/1.06  fof(f40,plain,(
% 2.49/1.06    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | r1_tmap_1(X3,X0,X4,X6)) & sK7 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 2.49/1.06    introduced(choice_axiom,[])).
% 2.49/1.06  
% 2.49/1.06  fof(f39,plain,(
% 2.49/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,sK6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,sK6)) & sK6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.49/1.06    introduced(choice_axiom,[])).
% 2.49/1.06  
% 2.49/1.06  fof(f38,plain,(
% 2.49/1.06    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(X2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 2.49/1.06    introduced(choice_axiom,[])).
% 2.49/1.06  
% 2.49/1.06  fof(f37,plain,(
% 2.49/1.06    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7) | ~r1_tmap_1(X3,X0,sK4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7) | r1_tmap_1(X3,X0,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 2.49/1.06    introduced(choice_axiom,[])).
% 2.49/1.06  
% 2.49/1.06  fof(f36,plain,(
% 2.49/1.06    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7) | ~r1_tmap_1(sK3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7) | r1_tmap_1(sK3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 2.49/1.06    introduced(choice_axiom,[])).
% 2.49/1.06  
% 2.49/1.06  fof(f35,plain,(
% 2.49/1.06    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 2.49/1.06    introduced(choice_axiom,[])).
% 2.49/1.06  
% 2.49/1.06  fof(f34,plain,(
% 2.49/1.06    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.49/1.06    introduced(choice_axiom,[])).
% 2.49/1.06  
% 2.49/1.06  fof(f33,plain,(
% 2.49/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.49/1.06    introduced(choice_axiom,[])).
% 2.49/1.06  
% 2.49/1.06  fof(f41,plain,(
% 2.49/1.06    ((((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.49/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f32,f40,f39,f38,f37,f36,f35,f34,f33])).
% 2.49/1.06  
% 2.49/1.06  fof(f68,plain,(
% 2.49/1.06    m1_pre_topc(sK2,sK3)),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f69,plain,(
% 2.49/1.06    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f4,axiom,(
% 2.49/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.06  
% 2.49/1.06  fof(f15,plain,(
% 2.49/1.06    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.49/1.06    inference(ennf_transformation,[],[f4])).
% 2.49/1.06  
% 2.49/1.06  fof(f46,plain,(
% 2.49/1.06    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.49/1.06    inference(cnf_transformation,[],[f15])).
% 2.49/1.06  
% 2.49/1.06  fof(f3,axiom,(
% 2.49/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.06  
% 2.49/1.06  fof(f14,plain,(
% 2.49/1.06    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.49/1.06    inference(ennf_transformation,[],[f3])).
% 2.49/1.06  
% 2.49/1.06  fof(f45,plain,(
% 2.49/1.06    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.49/1.06    inference(cnf_transformation,[],[f14])).
% 2.49/1.06  
% 2.49/1.06  fof(f60,plain,(
% 2.49/1.06    l1_pre_topc(sK1)),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f1,axiom,(
% 2.49/1.06    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.06  
% 2.49/1.06  fof(f28,plain,(
% 2.49/1.06    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.49/1.06    inference(nnf_transformation,[],[f1])).
% 2.49/1.06  
% 2.49/1.06  fof(f43,plain,(
% 2.49/1.06    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.49/1.06    inference(cnf_transformation,[],[f28])).
% 2.49/1.06  
% 2.49/1.06  fof(f74,plain,(
% 2.49/1.06    r1_tarski(sK5,u1_struct_0(sK2))),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f64,plain,(
% 2.49/1.06    m1_pre_topc(sK3,sK1)),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f5,axiom,(
% 2.49/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.06  
% 2.49/1.06  fof(f16,plain,(
% 2.49/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.49/1.06    inference(ennf_transformation,[],[f5])).
% 2.49/1.06  
% 2.49/1.06  fof(f17,plain,(
% 2.49/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.49/1.06    inference(flattening,[],[f16])).
% 2.49/1.06  
% 2.49/1.06  fof(f47,plain,(
% 2.49/1.06    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.49/1.06    inference(cnf_transformation,[],[f17])).
% 2.49/1.06  
% 2.49/1.06  fof(f59,plain,(
% 2.49/1.06    v2_pre_topc(sK1)),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f72,plain,(
% 2.49/1.06    v3_pre_topc(sK5,sK1)),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f6,axiom,(
% 2.49/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 2.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.06  
% 2.49/1.06  fof(f18,plain,(
% 2.49/1.06    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/1.06    inference(ennf_transformation,[],[f6])).
% 2.49/1.06  
% 2.49/1.06  fof(f19,plain,(
% 2.49/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/1.06    inference(flattening,[],[f18])).
% 2.49/1.06  
% 2.49/1.06  fof(f49,plain,(
% 2.49/1.06    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/1.06    inference(cnf_transformation,[],[f19])).
% 2.49/1.06  
% 2.49/1.06  fof(f78,plain,(
% 2.49/1.06    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/1.06    inference(equality_resolution,[],[f49])).
% 2.49/1.06  
% 2.49/1.06  fof(f7,axiom,(
% 2.49/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.06  
% 2.49/1.06  fof(f20,plain,(
% 2.49/1.06    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.49/1.06    inference(ennf_transformation,[],[f7])).
% 2.49/1.06  
% 2.49/1.06  fof(f21,plain,(
% 2.49/1.06    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.49/1.06    inference(flattening,[],[f20])).
% 2.49/1.06  
% 2.49/1.06  fof(f29,plain,(
% 2.49/1.06    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.49/1.06    inference(nnf_transformation,[],[f21])).
% 2.49/1.06  
% 2.49/1.06  fof(f51,plain,(
% 2.49/1.06    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.49/1.06    inference(cnf_transformation,[],[f29])).
% 2.49/1.06  
% 2.49/1.06  fof(f73,plain,(
% 2.49/1.06    r2_hidden(sK6,sK5)),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f9,axiom,(
% 2.49/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.06  
% 2.49/1.06  fof(f24,plain,(
% 2.49/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.49/1.06    inference(ennf_transformation,[],[f9])).
% 2.49/1.06  
% 2.49/1.06  fof(f25,plain,(
% 2.49/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.49/1.06    inference(flattening,[],[f24])).
% 2.49/1.06  
% 2.49/1.06  fof(f30,plain,(
% 2.49/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.49/1.06    inference(nnf_transformation,[],[f25])).
% 2.49/1.06  
% 2.49/1.06  fof(f53,plain,(
% 2.49/1.06    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.49/1.06    inference(cnf_transformation,[],[f30])).
% 2.49/1.06  
% 2.49/1.06  fof(f80,plain,(
% 2.49/1.06    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.49/1.06    inference(equality_resolution,[],[f53])).
% 2.49/1.06  
% 2.49/1.06  fof(f66,plain,(
% 2.49/1.06    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f65,plain,(
% 2.49/1.06    v1_funct_1(sK4)),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f8,axiom,(
% 2.49/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.06  
% 2.49/1.06  fof(f22,plain,(
% 2.49/1.06    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.49/1.06    inference(ennf_transformation,[],[f8])).
% 2.49/1.06  
% 2.49/1.06  fof(f23,plain,(
% 2.49/1.06    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.49/1.06    inference(flattening,[],[f22])).
% 2.49/1.06  
% 2.49/1.06  fof(f52,plain,(
% 2.49/1.06    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.49/1.06    inference(cnf_transformation,[],[f23])).
% 2.49/1.06  
% 2.49/1.06  fof(f2,axiom,(
% 2.49/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.49/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.06  
% 2.49/1.06  fof(f12,plain,(
% 2.49/1.06    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.49/1.06    inference(ennf_transformation,[],[f2])).
% 2.49/1.06  
% 2.49/1.06  fof(f13,plain,(
% 2.49/1.06    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.49/1.06    inference(flattening,[],[f12])).
% 2.49/1.06  
% 2.49/1.06  fof(f44,plain,(
% 2.49/1.06    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.49/1.06    inference(cnf_transformation,[],[f13])).
% 2.49/1.06  
% 2.49/1.06  fof(f75,plain,(
% 2.49/1.06    sK6 = sK7),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f55,plain,(
% 2.49/1.06    ~v2_struct_0(sK0)),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f56,plain,(
% 2.49/1.06    v2_pre_topc(sK0)),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f57,plain,(
% 2.49/1.06    l1_pre_topc(sK0)),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f63,plain,(
% 2.49/1.06    ~v2_struct_0(sK3)),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f67,plain,(
% 2.49/1.06    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f70,plain,(
% 2.49/1.06    m1_subset_1(sK6,u1_struct_0(sK3))),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f58,plain,(
% 2.49/1.06    ~v2_struct_0(sK1)),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f61,plain,(
% 2.49/1.06    ~v2_struct_0(sK2)),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f71,plain,(
% 2.49/1.06    m1_subset_1(sK7,u1_struct_0(sK2))),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f76,plain,(
% 2.49/1.06    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  fof(f54,plain,(
% 2.49/1.06    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.49/1.06    inference(cnf_transformation,[],[f30])).
% 2.49/1.06  
% 2.49/1.06  fof(f79,plain,(
% 2.49/1.06    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.49/1.06    inference(equality_resolution,[],[f54])).
% 2.49/1.06  
% 2.49/1.06  fof(f77,plain,(
% 2.49/1.06    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 2.49/1.06    inference(cnf_transformation,[],[f41])).
% 2.49/1.06  
% 2.49/1.06  cnf(c_22,negated_conjecture,
% 2.49/1.06      ( m1_pre_topc(sK2,sK3) ),
% 2.49/1.06      inference(cnf_transformation,[],[f68]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1601,negated_conjecture,
% 2.49/1.06      ( m1_pre_topc(sK2,sK3) ),
% 2.49/1.06      inference(subtyping,[status(esa)],[c_22]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_2420,plain,
% 2.49/1.06      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_1601]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_21,negated_conjecture,
% 2.49/1.06      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.49/1.06      inference(cnf_transformation,[],[f69]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1602,negated_conjecture,
% 2.49/1.06      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.49/1.06      inference(subtyping,[status(esa)],[c_21]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_2419,plain,
% 2.49/1.06      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_1602]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_4,plain,
% 2.49/1.06      ( ~ m1_pre_topc(X0,X1)
% 2.49/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.49/1.06      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.06      | ~ l1_pre_topc(X1) ),
% 2.49/1.06      inference(cnf_transformation,[],[f46]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1614,plain,
% 2.49/1.06      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.49/1.06      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.49/1.06      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X1_53)))
% 2.49/1.06      | ~ l1_pre_topc(X1_53) ),
% 2.49/1.06      inference(subtyping,[status(esa)],[c_4]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_2404,plain,
% 2.49/1.06      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.49/1.06      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/1.06      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X1_53))) = iProver_top
% 2.49/1.06      | l1_pre_topc(X1_53) != iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_1614]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_3347,plain,
% 2.49/1.06      ( m1_pre_topc(sK1,X0_53) != iProver_top
% 2.49/1.06      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53))) = iProver_top
% 2.49/1.06      | l1_pre_topc(X0_53) != iProver_top ),
% 2.49/1.06      inference(superposition,[status(thm)],[c_2419,c_2404]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_3871,plain,
% 2.49/1.06      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.49/1.06      | m1_pre_topc(sK1,X0_53) != iProver_top
% 2.49/1.06      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1_53))) = iProver_top
% 2.49/1.06      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.06      | l1_pre_topc(X0_53) != iProver_top ),
% 2.49/1.06      inference(superposition,[status(thm)],[c_3347,c_2404]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_3,plain,
% 2.49/1.06      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.49/1.06      inference(cnf_transformation,[],[f45]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1615,plain,
% 2.49/1.06      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.49/1.06      | ~ l1_pre_topc(X1_53)
% 2.49/1.06      | l1_pre_topc(X0_53) ),
% 2.49/1.06      inference(subtyping,[status(esa)],[c_3]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1654,plain,
% 2.49/1.06      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.49/1.06      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.06      | l1_pre_topc(X0_53) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_1615]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_4489,plain,
% 2.49/1.06      ( l1_pre_topc(X1_53) != iProver_top
% 2.49/1.06      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1_53))) = iProver_top
% 2.49/1.06      | m1_pre_topc(sK1,X0_53) != iProver_top
% 2.49/1.06      | m1_pre_topc(X0_53,X1_53) != iProver_top ),
% 2.49/1.06      inference(global_propositional_subsumption,
% 2.49/1.06                [status(thm)],
% 2.49/1.06                [c_3871,c_1654]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_4490,plain,
% 2.49/1.06      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.49/1.06      | m1_pre_topc(sK1,X0_53) != iProver_top
% 2.49/1.06      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1_53))) = iProver_top
% 2.49/1.06      | l1_pre_topc(X1_53) != iProver_top ),
% 2.49/1.06      inference(renaming,[status(thm)],[c_4489]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_4497,plain,
% 2.49/1.06      ( m1_pre_topc(sK1,sK2) != iProver_top
% 2.49/1.06      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.49/1.06      | l1_pre_topc(sK3) != iProver_top ),
% 2.49/1.06      inference(superposition,[status(thm)],[c_2420,c_4490]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_30,negated_conjecture,
% 2.49/1.06      ( l1_pre_topc(sK1) ),
% 2.49/1.06      inference(cnf_transformation,[],[f60]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_41,plain,
% 2.49/1.06      ( l1_pre_topc(sK1) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_49,plain,
% 2.49/1.06      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_0,plain,
% 2.49/1.06      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.49/1.06      inference(cnf_transformation,[],[f43]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_233,plain,
% 2.49/1.06      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.49/1.06      inference(prop_impl,[status(thm)],[c_0]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_16,negated_conjecture,
% 2.49/1.06      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 2.49/1.06      inference(cnf_transformation,[],[f74]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_774,plain,
% 2.49/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.49/1.06      | u1_struct_0(sK2) != X1
% 2.49/1.06      | sK5 != X0 ),
% 2.49/1.06      inference(resolution_lifted,[status(thm)],[c_233,c_16]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_775,plain,
% 2.49/1.06      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.49/1.06      inference(unflattening,[status(thm)],[c_774]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_776,plain,
% 2.49/1.06      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_775]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_26,negated_conjecture,
% 2.49/1.06      ( m1_pre_topc(sK3,sK1) ),
% 2.49/1.06      inference(cnf_transformation,[],[f64]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1599,negated_conjecture,
% 2.49/1.06      ( m1_pre_topc(sK3,sK1) ),
% 2.49/1.06      inference(subtyping,[status(esa)],[c_26]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_2422,plain,
% 2.49/1.06      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_1599]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_2403,plain,
% 2.49/1.06      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.49/1.06      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.06      | l1_pre_topc(X0_53) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_1615]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_3261,plain,
% 2.49/1.06      ( l1_pre_topc(sK3) = iProver_top
% 2.49/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 2.49/1.06      inference(superposition,[status(thm)],[c_2422,c_2403]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_2768,plain,
% 2.49/1.06      ( ~ m1_pre_topc(sK2,sK3)
% 2.49/1.06      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.06      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.06      | ~ l1_pre_topc(sK3) ),
% 2.49/1.06      inference(instantiation,[status(thm)],[c_1614]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_3502,plain,
% 2.49/1.06      ( ~ m1_pre_topc(sK2,sK3)
% 2.49/1.06      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.06      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.06      | ~ l1_pre_topc(sK3) ),
% 2.49/1.06      inference(instantiation,[status(thm)],[c_2768]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_3503,plain,
% 2.49/1.06      ( m1_pre_topc(sK2,sK3) != iProver_top
% 2.49/1.06      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.49/1.06      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.49/1.06      | l1_pre_topc(sK3) != iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_3502]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_4508,plain,
% 2.49/1.06      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.49/1.06      inference(global_propositional_subsumption,
% 2.49/1.06                [status(thm)],
% 2.49/1.06                [c_4497,c_41,c_49,c_776,c_3261,c_3503]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_6,plain,
% 2.49/1.06      ( ~ v3_pre_topc(X0,X1)
% 2.49/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.49/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.06      | ~ l1_pre_topc(X3)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X3)
% 2.49/1.06      | k1_tops_1(X1,X0) = X0 ),
% 2.49/1.06      inference(cnf_transformation,[],[f47]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1612,plain,
% 2.49/1.06      ( ~ v3_pre_topc(X0_54,X0_53)
% 2.49/1.06      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.49/1.06      | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X1_53)))
% 2.49/1.06      | ~ l1_pre_topc(X1_53)
% 2.49/1.06      | ~ l1_pre_topc(X0_53)
% 2.49/1.06      | ~ v2_pre_topc(X1_53)
% 2.49/1.06      | k1_tops_1(X0_53,X0_54) = X0_54 ),
% 2.49/1.06      inference(subtyping,[status(esa)],[c_6]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1623,plain,
% 2.49/1.06      ( ~ v3_pre_topc(X0_54,X0_53)
% 2.49/1.06      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.49/1.06      | ~ l1_pre_topc(X0_53)
% 2.49/1.06      | k1_tops_1(X0_53,X0_54) = X0_54
% 2.49/1.06      | ~ sP3_iProver_split ),
% 2.49/1.06      inference(splitting,
% 2.49/1.06                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 2.49/1.06                [c_1612]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_2409,plain,
% 2.49/1.06      ( k1_tops_1(X0_53,X0_54) = X0_54
% 2.49/1.06      | v3_pre_topc(X0_54,X0_53) != iProver_top
% 2.49/1.06      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/1.06      | l1_pre_topc(X0_53) != iProver_top
% 2.49/1.06      | sP3_iProver_split != iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_1623]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_31,negated_conjecture,
% 2.49/1.06      ( v2_pre_topc(sK1) ),
% 2.49/1.06      inference(cnf_transformation,[],[f59]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_40,plain,
% 2.49/1.06      ( v2_pre_topc(sK1) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_50,plain,
% 2.49/1.06      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1624,plain,
% 2.49/1.06      ( sP3_iProver_split | sP2_iProver_split ),
% 2.49/1.06      inference(splitting,
% 2.49/1.06                [splitting(split),new_symbols(definition,[])],
% 2.49/1.06                [c_1612]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1663,plain,
% 2.49/1.06      ( sP3_iProver_split = iProver_top
% 2.49/1.06      | sP2_iProver_split = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_1624]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1664,plain,
% 2.49/1.06      ( k1_tops_1(X0_53,X0_54) = X0_54
% 2.49/1.06      | v3_pre_topc(X0_54,X0_53) != iProver_top
% 2.49/1.06      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/1.06      | l1_pre_topc(X0_53) != iProver_top
% 2.49/1.06      | sP3_iProver_split != iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_1623]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1622,plain,
% 2.49/1.06      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.49/1.06      | ~ l1_pre_topc(X0_53)
% 2.49/1.06      | ~ v2_pre_topc(X0_53)
% 2.49/1.06      | ~ sP2_iProver_split ),
% 2.49/1.06      inference(splitting,
% 2.49/1.06                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.49/1.06                [c_1612]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_3074,plain,
% 2.49/1.06      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.49/1.06      | ~ l1_pre_topc(sK1)
% 2.49/1.06      | ~ v2_pre_topc(sK1)
% 2.49/1.06      | ~ sP2_iProver_split ),
% 2.49/1.06      inference(instantiation,[status(thm)],[c_1622]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_3075,plain,
% 2.49/1.06      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.49/1.06      | l1_pre_topc(sK1) != iProver_top
% 2.49/1.06      | v2_pre_topc(sK1) != iProver_top
% 2.49/1.06      | sP2_iProver_split != iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_3074]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_4672,plain,
% 2.49/1.06      ( l1_pre_topc(X0_53) != iProver_top
% 2.49/1.06      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/1.06      | v3_pre_topc(X0_54,X0_53) != iProver_top
% 2.49/1.06      | k1_tops_1(X0_53,X0_54) = X0_54 ),
% 2.49/1.06      inference(global_propositional_subsumption,
% 2.49/1.06                [status(thm)],
% 2.49/1.06                [c_2409,c_40,c_41,c_50,c_1663,c_1664,c_3075]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_4673,plain,
% 2.49/1.06      ( k1_tops_1(X0_53,X0_54) = X0_54
% 2.49/1.06      | v3_pre_topc(X0_54,X0_53) != iProver_top
% 2.49/1.06      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/1.06      | l1_pre_topc(X0_53) != iProver_top ),
% 2.49/1.06      inference(renaming,[status(thm)],[c_4672]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_4687,plain,
% 2.49/1.06      ( k1_tops_1(sK3,sK5) = sK5
% 2.49/1.06      | v3_pre_topc(sK5,sK3) != iProver_top
% 2.49/1.06      | l1_pre_topc(sK3) != iProver_top ),
% 2.49/1.06      inference(superposition,[status(thm)],[c_4508,c_4673]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_18,negated_conjecture,
% 2.49/1.06      ( v3_pre_topc(sK5,sK1) ),
% 2.49/1.06      inference(cnf_transformation,[],[f72]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_7,plain,
% 2.49/1.06      ( ~ v3_pre_topc(X0,X1)
% 2.49/1.06      | v3_pre_topc(X0,X2)
% 2.49/1.06      | ~ m1_pre_topc(X2,X1)
% 2.49/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.06      | ~ l1_pre_topc(X1) ),
% 2.49/1.06      inference(cnf_transformation,[],[f78]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1611,plain,
% 2.49/1.06      ( ~ v3_pre_topc(X0_54,X0_53)
% 2.49/1.06      | v3_pre_topc(X0_54,X1_53)
% 2.49/1.06      | ~ m1_pre_topc(X1_53,X0_53)
% 2.49/1.06      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X1_53)))
% 2.49/1.06      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.49/1.06      | ~ l1_pre_topc(X0_53) ),
% 2.49/1.06      inference(subtyping,[status(esa)],[c_7]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_2831,plain,
% 2.49/1.06      ( v3_pre_topc(sK5,X0_53)
% 2.49/1.06      | ~ v3_pre_topc(sK5,sK1)
% 2.49/1.06      | ~ m1_pre_topc(X0_53,sK1)
% 2.49/1.06      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.49/1.06      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.49/1.06      | ~ l1_pre_topc(sK1) ),
% 2.49/1.06      inference(instantiation,[status(thm)],[c_1611]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_3102,plain,
% 2.49/1.06      ( v3_pre_topc(sK5,sK3)
% 2.49/1.06      | ~ v3_pre_topc(sK5,sK1)
% 2.49/1.06      | ~ m1_pre_topc(sK3,sK1)
% 2.49/1.06      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.06      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.49/1.06      | ~ l1_pre_topc(sK1) ),
% 2.49/1.06      inference(instantiation,[status(thm)],[c_2831]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_3276,plain,
% 2.49/1.06      ( l1_pre_topc(sK3) | ~ l1_pre_topc(sK1) ),
% 2.49/1.06      inference(predicate_to_equality_rev,[status(thm)],[c_3261]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_2932,plain,
% 2.49/1.06      ( ~ v3_pre_topc(sK5,X0_53)
% 2.49/1.06      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.49/1.06      | ~ l1_pre_topc(X0_53)
% 2.49/1.06      | ~ sP3_iProver_split
% 2.49/1.06      | k1_tops_1(X0_53,sK5) = sK5 ),
% 2.49/1.06      inference(instantiation,[status(thm)],[c_1623]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_3660,plain,
% 2.49/1.06      ( ~ v3_pre_topc(sK5,sK3)
% 2.49/1.06      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.06      | ~ l1_pre_topc(sK3)
% 2.49/1.06      | ~ sP3_iProver_split
% 2.49/1.06      | k1_tops_1(sK3,sK5) = sK5 ),
% 2.49/1.06      inference(instantiation,[status(thm)],[c_2932]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_5038,plain,
% 2.49/1.06      ( k1_tops_1(sK3,sK5) = sK5 ),
% 2.49/1.06      inference(global_propositional_subsumption,
% 2.49/1.06                [status(thm)],
% 2.49/1.06                [c_4687,c_31,c_30,c_26,c_22,c_21,c_18,c_775,c_1624,
% 2.49/1.06                 c_3074,c_3102,c_3276,c_3502,c_3660]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_8,plain,
% 2.49/1.06      ( m1_connsp_2(X0,X1,X2)
% 2.49/1.06      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.49/1.06      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.49/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X1) ),
% 2.49/1.06      inference(cnf_transformation,[],[f51]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_17,negated_conjecture,
% 2.49/1.06      ( r2_hidden(sK6,sK5) ),
% 2.49/1.06      inference(cnf_transformation,[],[f73]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_442,plain,
% 2.49/1.06      ( m1_connsp_2(X0,X1,X2)
% 2.49/1.06      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.49/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | k1_tops_1(X1,X0) != sK5
% 2.49/1.06      | sK6 != X2 ),
% 2.49/1.06      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_443,plain,
% 2.49/1.06      ( m1_connsp_2(X0,X1,sK6)
% 2.49/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.06      | ~ m1_subset_1(sK6,u1_struct_0(X1))
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | k1_tops_1(X1,X0) != sK5 ),
% 2.49/1.06      inference(unflattening,[status(thm)],[c_442]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_12,plain,
% 2.49/1.06      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.49/1.06      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.49/1.06      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.49/1.06      | ~ m1_connsp_2(X6,X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X4,X5)
% 2.49/1.06      | ~ m1_pre_topc(X4,X0)
% 2.49/1.06      | ~ m1_pre_topc(X0,X5)
% 2.49/1.06      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.49/1.06      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.49/1.06      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.49/1.06      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.49/1.06      | ~ v1_funct_1(X2)
% 2.49/1.06      | v2_struct_0(X5)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X4)
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | ~ l1_pre_topc(X5)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X5)
% 2.49/1.06      | ~ v2_pre_topc(X1) ),
% 2.49/1.06      inference(cnf_transformation,[],[f80]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_24,negated_conjecture,
% 2.49/1.06      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
% 2.49/1.06      inference(cnf_transformation,[],[f66]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_477,plain,
% 2.49/1.06      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.49/1.06      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.49/1.06      | ~ m1_connsp_2(X6,X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X4,X5)
% 2.49/1.06      | ~ m1_pre_topc(X4,X0)
% 2.49/1.06      | ~ m1_pre_topc(X0,X5)
% 2.49/1.06      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.49/1.06      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.49/1.06      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.49/1.06      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.49/1.06      | ~ v1_funct_1(X2)
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X5)
% 2.49/1.06      | v2_struct_0(X4)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ l1_pre_topc(X5)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X5)
% 2.49/1.06      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.49/1.06      | sK4 != X2 ),
% 2.49/1.06      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_478,plain,
% 2.49/1.06      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.49/1.06      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.49/1.06      | ~ m1_connsp_2(X5,X3,X4)
% 2.49/1.06      | ~ m1_pre_topc(X0,X2)
% 2.49/1.06      | ~ m1_pre_topc(X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X3,X2)
% 2.49/1.06      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.49/1.06      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.49/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.49/1.06      | ~ v1_funct_1(sK4)
% 2.49/1.06      | v2_struct_0(X3)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X2)
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ l1_pre_topc(X2)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X2)
% 2.49/1.06      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.49/1.06      inference(unflattening,[status(thm)],[c_477]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_25,negated_conjecture,
% 2.49/1.06      ( v1_funct_1(sK4) ),
% 2.49/1.06      inference(cnf_transformation,[],[f65]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_482,plain,
% 2.49/1.06      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.49/1.06      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.49/1.06      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_pre_topc(X3,X2)
% 2.49/1.06      | ~ m1_pre_topc(X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X0,X2)
% 2.49/1.06      | ~ m1_connsp_2(X5,X3,X4)
% 2.49/1.06      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.49/1.06      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.49/1.06      | v2_struct_0(X3)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X2)
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ l1_pre_topc(X2)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X2)
% 2.49/1.06      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.49/1.06      inference(global_propositional_subsumption,
% 2.49/1.06                [status(thm)],
% 2.49/1.06                [c_478,c_25]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_483,plain,
% 2.49/1.06      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.49/1.06      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.49/1.06      | ~ m1_connsp_2(X5,X3,X4)
% 2.49/1.06      | ~ m1_pre_topc(X0,X2)
% 2.49/1.06      | ~ m1_pre_topc(X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X3,X2)
% 2.49/1.06      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.49/1.06      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.49/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X2)
% 2.49/1.06      | v2_struct_0(X3)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ l1_pre_topc(X2)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X2)
% 2.49/1.06      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.49/1.06      inference(renaming,[status(thm)],[c_482]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_10,plain,
% 2.49/1.06      ( ~ m1_pre_topc(X0,X1)
% 2.49/1.06      | ~ m1_pre_topc(X2,X0)
% 2.49/1.06      | m1_pre_topc(X2,X1)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X1) ),
% 2.49/1.06      inference(cnf_transformation,[],[f52]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_530,plain,
% 2.49/1.06      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.49/1.06      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.49/1.06      | ~ m1_connsp_2(X5,X3,X4)
% 2.49/1.06      | ~ m1_pre_topc(X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X3,X2)
% 2.49/1.06      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.49/1.06      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.49/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X2)
% 2.49/1.06      | v2_struct_0(X3)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ l1_pre_topc(X2)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X2)
% 2.49/1.06      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.49/1.06      inference(forward_subsumption_resolution,
% 2.49/1.06                [status(thm)],
% 2.49/1.06                [c_483,c_10]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_700,plain,
% 2.49/1.06      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.49/1.06      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.49/1.06      | ~ m1_pre_topc(X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X3,X2)
% 2.49/1.06      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
% 2.49/1.06      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.49/1.06      | ~ m1_subset_1(sK6,u1_struct_0(X7))
% 2.49/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.49/1.06      | v2_struct_0(X7)
% 2.49/1.06      | v2_struct_0(X3)
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X2)
% 2.49/1.06      | ~ l1_pre_topc(X7)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ l1_pre_topc(X2)
% 2.49/1.06      | ~ v2_pre_topc(X7)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X2)
% 2.49/1.06      | X5 != X6
% 2.49/1.06      | X3 != X7
% 2.49/1.06      | k1_tops_1(X7,X6) != sK5
% 2.49/1.06      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.49/1.06      | sK6 != X4 ),
% 2.49/1.06      inference(resolution_lifted,[status(thm)],[c_443,c_530]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_701,plain,
% 2.49/1.06      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 2.49/1.06      | ~ r1_tmap_1(X3,X1,sK4,sK6)
% 2.49/1.06      | ~ m1_pre_topc(X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X3,X2)
% 2.49/1.06      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
% 2.49/1.06      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.49/1.06      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X2)
% 2.49/1.06      | v2_struct_0(X3)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ l1_pre_topc(X2)
% 2.49/1.06      | ~ l1_pre_topc(X3)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X2)
% 2.49/1.06      | ~ v2_pre_topc(X3)
% 2.49/1.06      | k1_tops_1(X3,X4) != sK5
% 2.49/1.06      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.49/1.06      inference(unflattening,[status(thm)],[c_700]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_2,plain,
% 2.49/1.06      ( ~ m1_pre_topc(X0,X1)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | v2_pre_topc(X0) ),
% 2.49/1.06      inference(cnf_transformation,[],[f44]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_749,plain,
% 2.49/1.06      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 2.49/1.06      | ~ r1_tmap_1(X3,X1,sK4,sK6)
% 2.49/1.06      | ~ m1_pre_topc(X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X3,X2)
% 2.49/1.06      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
% 2.49/1.06      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.49/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X2)
% 2.49/1.06      | v2_struct_0(X3)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ l1_pre_topc(X2)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X2)
% 2.49/1.06      | k1_tops_1(X3,X4) != sK5
% 2.49/1.06      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.49/1.06      inference(forward_subsumption_resolution,
% 2.49/1.06                [status(thm)],
% 2.49/1.06                [c_701,c_2,c_3]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1588,plain,
% 2.49/1.06      ( r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),sK6)
% 2.49/1.06      | ~ r1_tmap_1(X3_53,X1_53,sK4,sK6)
% 2.49/1.06      | ~ m1_pre_topc(X0_53,X3_53)
% 2.49/1.06      | ~ m1_pre_topc(X3_53,X2_53)
% 2.49/1.06      | ~ r1_tarski(X0_54,u1_struct_0(X0_53))
% 2.49/1.06      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X3_53)))
% 2.49/1.06      | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
% 2.49/1.06      | ~ m1_subset_1(sK6,u1_struct_0(X3_53))
% 2.49/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
% 2.49/1.06      | v2_struct_0(X0_53)
% 2.49/1.06      | v2_struct_0(X1_53)
% 2.49/1.06      | v2_struct_0(X2_53)
% 2.49/1.06      | v2_struct_0(X3_53)
% 2.49/1.06      | ~ l1_pre_topc(X1_53)
% 2.49/1.06      | ~ l1_pre_topc(X2_53)
% 2.49/1.06      | ~ v2_pre_topc(X1_53)
% 2.49/1.06      | ~ v2_pre_topc(X2_53)
% 2.49/1.06      | u1_struct_0(X3_53) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1_53) != u1_struct_0(sK0)
% 2.49/1.06      | k1_tops_1(X3_53,X0_54) != sK5 ),
% 2.49/1.06      inference(subtyping,[status(esa)],[c_749]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_2433,plain,
% 2.49/1.06      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1_53) != u1_struct_0(sK0)
% 2.49/1.06      | k1_tops_1(X0_53,X0_54) != sK5
% 2.49/1.06      | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4),sK6) = iProver_top
% 2.49/1.06      | r1_tmap_1(X0_53,X1_53,sK4,sK6) != iProver_top
% 2.49/1.06      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 2.49/1.06      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 2.49/1.06      | r1_tarski(X0_54,u1_struct_0(X2_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/1.06      | m1_subset_1(sK6,u1_struct_0(X2_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(sK6,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.49/1.06      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.06      | v2_struct_0(X2_53) = iProver_top
% 2.49/1.06      | v2_struct_0(X3_53) = iProver_top
% 2.49/1.06      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.06      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.06      | l1_pre_topc(X3_53) != iProver_top
% 2.49/1.06      | v2_pre_topc(X1_53) != iProver_top
% 2.49/1.06      | v2_pre_topc(X3_53) != iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_1588]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_15,negated_conjecture,
% 2.49/1.06      ( sK6 = sK7 ),
% 2.49/1.06      inference(cnf_transformation,[],[f75]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1607,negated_conjecture,
% 2.49/1.06      ( sK6 = sK7 ),
% 2.49/1.06      inference(subtyping,[status(esa)],[c_15]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_2618,plain,
% 2.49/1.06      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1_53) != u1_struct_0(sK0)
% 2.49/1.06      | k1_tops_1(X0_53,X0_54) != sK5
% 2.49/1.06      | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4),sK7) = iProver_top
% 2.49/1.06      | r1_tmap_1(X0_53,X1_53,sK4,sK7) != iProver_top
% 2.49/1.06      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 2.49/1.06      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 2.49/1.06      | r1_tarski(X0_54,u1_struct_0(X2_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/1.06      | m1_subset_1(sK7,u1_struct_0(X2_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.49/1.06      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.06      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.06      | v2_struct_0(X2_53) = iProver_top
% 2.49/1.06      | v2_struct_0(X3_53) = iProver_top
% 2.49/1.06      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.06      | l1_pre_topc(X3_53) != iProver_top
% 2.49/1.06      | v2_pre_topc(X1_53) != iProver_top
% 2.49/1.06      | v2_pre_topc(X3_53) != iProver_top ),
% 2.49/1.06      inference(light_normalisation,[status(thm)],[c_2433,c_1607]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_3498,plain,
% 2.49/1.06      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.49/1.06      | k1_tops_1(X0_53,X0_54) != sK5
% 2.49/1.06      | r1_tmap_1(X1_53,sK0,k3_tmap_1(X2_53,sK0,X0_53,X1_53,sK4),sK7) = iProver_top
% 2.49/1.06      | r1_tmap_1(X0_53,sK0,sK4,sK7) != iProver_top
% 2.49/1.06      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.49/1.06      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.49/1.06      | r1_tarski(X0_54,u1_struct_0(X1_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/1.06      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK0)))) != iProver_top
% 2.49/1.06      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.06      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.06      | v2_struct_0(X2_53) = iProver_top
% 2.49/1.06      | v2_struct_0(sK0) = iProver_top
% 2.49/1.06      | l1_pre_topc(X2_53) != iProver_top
% 2.49/1.06      | l1_pre_topc(sK0) != iProver_top
% 2.49/1.06      | v2_pre_topc(X2_53) != iProver_top
% 2.49/1.06      | v2_pre_topc(sK0) != iProver_top ),
% 2.49/1.06      inference(equality_resolution,[status(thm)],[c_2618]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_35,negated_conjecture,
% 2.49/1.06      ( ~ v2_struct_0(sK0) ),
% 2.49/1.06      inference(cnf_transformation,[],[f55]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_36,plain,
% 2.49/1.06      ( v2_struct_0(sK0) != iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_34,negated_conjecture,
% 2.49/1.06      ( v2_pre_topc(sK0) ),
% 2.49/1.06      inference(cnf_transformation,[],[f56]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_37,plain,
% 2.49/1.06      ( v2_pre_topc(sK0) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_33,negated_conjecture,
% 2.49/1.06      ( l1_pre_topc(sK0) ),
% 2.49/1.06      inference(cnf_transformation,[],[f57]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_38,plain,
% 2.49/1.06      ( l1_pre_topc(sK0) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_4104,plain,
% 2.49/1.06      ( v2_pre_topc(X2_53) != iProver_top
% 2.49/1.06      | v2_struct_0(X2_53) = iProver_top
% 2.49/1.06      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.06      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK0)))) != iProver_top
% 2.49/1.06      | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/1.06      | r1_tarski(X0_54,u1_struct_0(X1_53)) != iProver_top
% 2.49/1.06      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.49/1.06      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.49/1.06      | r1_tmap_1(X0_53,sK0,sK4,sK7) != iProver_top
% 2.49/1.06      | r1_tmap_1(X1_53,sK0,k3_tmap_1(X2_53,sK0,X0_53,X1_53,sK4),sK7) = iProver_top
% 2.49/1.06      | k1_tops_1(X0_53,X0_54) != sK5
% 2.49/1.06      | u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.49/1.06      | l1_pre_topc(X2_53) != iProver_top ),
% 2.49/1.06      inference(global_propositional_subsumption,
% 2.49/1.06                [status(thm)],
% 2.49/1.06                [c_3498,c_36,c_37,c_38]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_4105,plain,
% 2.49/1.06      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.49/1.06      | k1_tops_1(X0_53,X0_54) != sK5
% 2.49/1.06      | r1_tmap_1(X1_53,sK0,k3_tmap_1(X2_53,sK0,X0_53,X1_53,sK4),sK7) = iProver_top
% 2.49/1.06      | r1_tmap_1(X0_53,sK0,sK4,sK7) != iProver_top
% 2.49/1.06      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.49/1.06      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.49/1.06      | r1_tarski(X0_54,u1_struct_0(X1_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/1.06      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK0)))) != iProver_top
% 2.49/1.06      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.06      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.06      | v2_struct_0(X2_53) = iProver_top
% 2.49/1.06      | l1_pre_topc(X2_53) != iProver_top
% 2.49/1.06      | v2_pre_topc(X2_53) != iProver_top ),
% 2.49/1.06      inference(renaming,[status(thm)],[c_4104]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_4124,plain,
% 2.49/1.06      ( k1_tops_1(sK3,X0_54) != sK5
% 2.49/1.06      | r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) = iProver_top
% 2.49/1.06      | r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
% 2.49/1.06      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.49/1.06      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.49/1.06      | r1_tarski(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.06      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.49/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 2.49/1.06      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.06      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.06      | v2_struct_0(sK3) = iProver_top
% 2.49/1.06      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.06      | v2_pre_topc(X1_53) != iProver_top ),
% 2.49/1.06      inference(equality_resolution,[status(thm)],[c_4105]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_27,negated_conjecture,
% 2.49/1.06      ( ~ v2_struct_0(sK3) ),
% 2.49/1.06      inference(cnf_transformation,[],[f63]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_44,plain,
% 2.49/1.06      ( v2_struct_0(sK3) != iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_23,negated_conjecture,
% 2.49/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
% 2.49/1.06      inference(cnf_transformation,[],[f67]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_48,plain,
% 2.49/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_20,negated_conjecture,
% 2.49/1.06      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.49/1.06      inference(cnf_transformation,[],[f70]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1603,negated_conjecture,
% 2.49/1.06      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.49/1.06      inference(subtyping,[status(esa)],[c_20]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_2418,plain,
% 2.49/1.06      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_1603]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_2464,plain,
% 2.49/1.06      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.49/1.06      inference(light_normalisation,[status(thm)],[c_2418,c_1607]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_5258,plain,
% 2.49/1.06      ( v2_struct_0(X0_53) = iProver_top
% 2.49/1.06      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.06      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.06      | r1_tarski(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.06      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.49/1.06      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.49/1.06      | r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
% 2.49/1.06      | r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) = iProver_top
% 2.49/1.06      | k1_tops_1(sK3,X0_54) != sK5
% 2.49/1.06      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.06      | v2_pre_topc(X1_53) != iProver_top ),
% 2.49/1.06      inference(global_propositional_subsumption,
% 2.49/1.06                [status(thm)],
% 2.49/1.06                [c_4124,c_44,c_48,c_2464]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_5259,plain,
% 2.49/1.06      ( k1_tops_1(sK3,X0_54) != sK5
% 2.49/1.06      | r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) = iProver_top
% 2.49/1.06      | r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
% 2.49/1.06      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.49/1.06      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.49/1.06      | r1_tarski(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.06      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.06      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.06      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.06      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.06      | v2_pre_topc(X1_53) != iProver_top ),
% 2.49/1.06      inference(renaming,[status(thm)],[c_5258]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_5276,plain,
% 2.49/1.06      ( r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) = iProver_top
% 2.49/1.06      | r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
% 2.49/1.06      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.49/1.06      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.49/1.06      | r1_tarski(sK5,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.06      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.06      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.06      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.06      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.06      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.06      | v2_pre_topc(X1_53) != iProver_top ),
% 2.49/1.06      inference(superposition,[status(thm)],[c_5038,c_5259]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_32,negated_conjecture,
% 2.49/1.06      ( ~ v2_struct_0(sK1) ),
% 2.49/1.06      inference(cnf_transformation,[],[f58]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_39,plain,
% 2.49/1.06      ( v2_struct_0(sK1) != iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_29,negated_conjecture,
% 2.49/1.06      ( ~ v2_struct_0(sK2) ),
% 2.49/1.06      inference(cnf_transformation,[],[f61]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_42,plain,
% 2.49/1.06      ( v2_struct_0(sK2) != iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_45,plain,
% 2.49/1.06      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_19,negated_conjecture,
% 2.49/1.06      ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
% 2.49/1.06      inference(cnf_transformation,[],[f71]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_52,plain,
% 2.49/1.06      ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_55,plain,
% 2.49/1.06      ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_14,negated_conjecture,
% 2.49/1.06      ( r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.49/1.06      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 2.49/1.06      inference(cnf_transformation,[],[f76]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1608,negated_conjecture,
% 2.49/1.06      ( r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.49/1.06      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 2.49/1.06      inference(subtyping,[status(esa)],[c_14]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_2414,plain,
% 2.49/1.06      ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 2.49/1.06      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
% 2.49/1.06      inference(predicate_to_equality,[status(thm)],[c_1608]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_2499,plain,
% 2.49/1.06      ( r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
% 2.49/1.06      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
% 2.49/1.06      inference(light_normalisation,[status(thm)],[c_2414,c_1607]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_11,plain,
% 2.49/1.06      ( r1_tmap_1(X0,X1,X2,X3)
% 2.49/1.06      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.49/1.06      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.49/1.06      | ~ m1_connsp_2(X6,X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X4,X5)
% 2.49/1.06      | ~ m1_pre_topc(X4,X0)
% 2.49/1.06      | ~ m1_pre_topc(X0,X5)
% 2.49/1.06      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.49/1.06      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.49/1.06      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.49/1.06      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.49/1.06      | ~ v1_funct_1(X2)
% 2.49/1.06      | v2_struct_0(X5)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X4)
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | ~ l1_pre_topc(X5)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X5)
% 2.49/1.06      | ~ v2_pre_topc(X1) ),
% 2.49/1.06      inference(cnf_transformation,[],[f79]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_552,plain,
% 2.49/1.06      ( r1_tmap_1(X0,X1,X2,X3)
% 2.49/1.06      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.49/1.06      | ~ m1_connsp_2(X6,X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X4,X5)
% 2.49/1.06      | ~ m1_pre_topc(X4,X0)
% 2.49/1.06      | ~ m1_pre_topc(X0,X5)
% 2.49/1.06      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.49/1.06      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.49/1.06      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.49/1.06      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.49/1.06      | ~ v1_funct_1(X2)
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X5)
% 2.49/1.06      | v2_struct_0(X4)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ l1_pre_topc(X5)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X5)
% 2.49/1.06      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.49/1.06      | sK4 != X2 ),
% 2.49/1.06      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_553,plain,
% 2.49/1.06      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.49/1.06      | r1_tmap_1(X3,X1,sK4,X4)
% 2.49/1.06      | ~ m1_connsp_2(X5,X3,X4)
% 2.49/1.06      | ~ m1_pre_topc(X0,X2)
% 2.49/1.06      | ~ m1_pre_topc(X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X3,X2)
% 2.49/1.06      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.49/1.06      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.49/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.49/1.06      | ~ v1_funct_1(sK4)
% 2.49/1.06      | v2_struct_0(X3)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X2)
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ l1_pre_topc(X2)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X2)
% 2.49/1.06      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.49/1.06      inference(unflattening,[status(thm)],[c_552]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_557,plain,
% 2.49/1.06      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.49/1.06      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.49/1.06      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_pre_topc(X3,X2)
% 2.49/1.06      | ~ m1_pre_topc(X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X0,X2)
% 2.49/1.06      | ~ m1_connsp_2(X5,X3,X4)
% 2.49/1.06      | r1_tmap_1(X3,X1,sK4,X4)
% 2.49/1.06      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.49/1.06      | v2_struct_0(X3)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X2)
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ l1_pre_topc(X2)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X2)
% 2.49/1.06      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.49/1.06      inference(global_propositional_subsumption,
% 2.49/1.06                [status(thm)],
% 2.49/1.06                [c_553,c_25]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_558,plain,
% 2.49/1.06      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.49/1.06      | r1_tmap_1(X3,X1,sK4,X4)
% 2.49/1.06      | ~ m1_connsp_2(X5,X3,X4)
% 2.49/1.06      | ~ m1_pre_topc(X0,X2)
% 2.49/1.06      | ~ m1_pre_topc(X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X3,X2)
% 2.49/1.06      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.49/1.06      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.49/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X2)
% 2.49/1.06      | v2_struct_0(X3)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ l1_pre_topc(X2)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X2)
% 2.49/1.06      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.49/1.06      inference(renaming,[status(thm)],[c_557]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_605,plain,
% 2.49/1.06      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.49/1.06      | r1_tmap_1(X3,X1,sK4,X4)
% 2.49/1.06      | ~ m1_connsp_2(X5,X3,X4)
% 2.49/1.06      | ~ m1_pre_topc(X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X3,X2)
% 2.49/1.06      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.49/1.06      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.49/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X2)
% 2.49/1.06      | v2_struct_0(X3)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ l1_pre_topc(X2)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X2)
% 2.49/1.06      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.49/1.06      inference(forward_subsumption_resolution,
% 2.49/1.06                [status(thm)],
% 2.49/1.06                [c_558,c_10]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_629,plain,
% 2.49/1.06      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.49/1.06      | r1_tmap_1(X3,X1,sK4,X4)
% 2.49/1.06      | ~ m1_pre_topc(X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X3,X2)
% 2.49/1.06      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.49/1.06      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
% 2.49/1.06      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.49/1.06      | ~ m1_subset_1(sK6,u1_struct_0(X7))
% 2.49/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.49/1.06      | v2_struct_0(X7)
% 2.49/1.06      | v2_struct_0(X3)
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X2)
% 2.49/1.06      | ~ l1_pre_topc(X7)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ l1_pre_topc(X2)
% 2.49/1.06      | ~ v2_pre_topc(X7)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X2)
% 2.49/1.06      | X5 != X6
% 2.49/1.06      | X3 != X7
% 2.49/1.06      | k1_tops_1(X7,X6) != sK5
% 2.49/1.06      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.49/1.06      | sK6 != X4 ),
% 2.49/1.06      inference(resolution_lifted,[status(thm)],[c_443,c_605]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_630,plain,
% 2.49/1.06      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 2.49/1.06      | r1_tmap_1(X3,X1,sK4,sK6)
% 2.49/1.06      | ~ m1_pre_topc(X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X3,X2)
% 2.49/1.06      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
% 2.49/1.06      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.49/1.06      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X2)
% 2.49/1.06      | v2_struct_0(X3)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ l1_pre_topc(X2)
% 2.49/1.06      | ~ l1_pre_topc(X3)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X2)
% 2.49/1.06      | ~ v2_pre_topc(X3)
% 2.49/1.06      | k1_tops_1(X3,X4) != sK5
% 2.49/1.06      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.49/1.06      inference(unflattening,[status(thm)],[c_629]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_678,plain,
% 2.49/1.06      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 2.49/1.06      | r1_tmap_1(X3,X1,sK4,sK6)
% 2.49/1.06      | ~ m1_pre_topc(X0,X3)
% 2.49/1.06      | ~ m1_pre_topc(X3,X2)
% 2.49/1.06      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
% 2.49/1.06      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.49/1.06      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.49/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.49/1.06      | v2_struct_0(X0)
% 2.49/1.06      | v2_struct_0(X1)
% 2.49/1.06      | v2_struct_0(X2)
% 2.49/1.06      | v2_struct_0(X3)
% 2.49/1.06      | ~ l1_pre_topc(X1)
% 2.49/1.06      | ~ l1_pre_topc(X2)
% 2.49/1.06      | ~ v2_pre_topc(X1)
% 2.49/1.06      | ~ v2_pre_topc(X2)
% 2.49/1.06      | k1_tops_1(X3,X4) != sK5
% 2.49/1.06      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.49/1.06      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.49/1.06      inference(forward_subsumption_resolution,
% 2.49/1.06                [status(thm)],
% 2.49/1.06                [c_630,c_2,c_3]) ).
% 2.49/1.06  
% 2.49/1.06  cnf(c_1589,plain,
% 2.49/1.06      ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),sK6)
% 2.49/1.06      | r1_tmap_1(X3_53,X1_53,sK4,sK6)
% 2.49/1.06      | ~ m1_pre_topc(X0_53,X3_53)
% 2.49/1.06      | ~ m1_pre_topc(X3_53,X2_53)
% 2.49/1.06      | ~ r1_tarski(X0_54,u1_struct_0(X0_53))
% 2.49/1.06      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X3_53)))
% 2.49/1.06      | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
% 2.49/1.06      | ~ m1_subset_1(sK6,u1_struct_0(X3_53))
% 2.49/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
% 2.49/1.07      | v2_struct_0(X0_53)
% 2.49/1.07      | v2_struct_0(X1_53)
% 2.49/1.07      | v2_struct_0(X2_53)
% 2.49/1.07      | v2_struct_0(X3_53)
% 2.49/1.07      | ~ l1_pre_topc(X1_53)
% 2.49/1.07      | ~ l1_pre_topc(X2_53)
% 2.49/1.07      | ~ v2_pre_topc(X1_53)
% 2.49/1.07      | ~ v2_pre_topc(X2_53)
% 2.49/1.07      | u1_struct_0(X3_53) != u1_struct_0(sK3)
% 2.49/1.07      | u1_struct_0(X1_53) != u1_struct_0(sK0)
% 2.49/1.07      | k1_tops_1(X3_53,X0_54) != sK5 ),
% 2.49/1.07      inference(subtyping,[status(esa)],[c_678]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_2432,plain,
% 2.49/1.07      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.49/1.07      | u1_struct_0(X1_53) != u1_struct_0(sK0)
% 2.49/1.07      | k1_tops_1(X0_53,X0_54) != sK5
% 2.49/1.07      | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4),sK6) != iProver_top
% 2.49/1.07      | r1_tmap_1(X0_53,X1_53,sK4,sK6) = iProver_top
% 2.49/1.07      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 2.49/1.07      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 2.49/1.07      | r1_tarski(X0_54,u1_struct_0(X2_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/1.07      | m1_subset_1(sK6,u1_struct_0(X2_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(sK6,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.49/1.07      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X2_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X3_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.07      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.07      | l1_pre_topc(X3_53) != iProver_top
% 2.49/1.07      | v2_pre_topc(X1_53) != iProver_top
% 2.49/1.07      | v2_pre_topc(X3_53) != iProver_top ),
% 2.49/1.07      inference(predicate_to_equality,[status(thm)],[c_1589]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_2577,plain,
% 2.49/1.07      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.49/1.07      | u1_struct_0(X1_53) != u1_struct_0(sK0)
% 2.49/1.07      | k1_tops_1(X0_53,X0_54) != sK5
% 2.49/1.07      | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4),sK7) != iProver_top
% 2.49/1.07      | r1_tmap_1(X0_53,X1_53,sK4,sK7) = iProver_top
% 2.49/1.07      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 2.49/1.07      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 2.49/1.07      | r1_tarski(X0_54,u1_struct_0(X2_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(X2_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.49/1.07      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X2_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X3_53) = iProver_top
% 2.49/1.07      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.07      | l1_pre_topc(X3_53) != iProver_top
% 2.49/1.07      | v2_pre_topc(X1_53) != iProver_top
% 2.49/1.07      | v2_pre_topc(X3_53) != iProver_top ),
% 2.49/1.07      inference(light_normalisation,[status(thm)],[c_2432,c_1607]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_3473,plain,
% 2.49/1.07      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.49/1.07      | k1_tops_1(X0_53,X0_54) != sK5
% 2.49/1.07      | r1_tmap_1(X1_53,sK0,k3_tmap_1(X2_53,sK0,X0_53,X1_53,sK4),sK7) != iProver_top
% 2.49/1.07      | r1_tmap_1(X0_53,sK0,sK4,sK7) = iProver_top
% 2.49/1.07      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.49/1.07      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.49/1.07      | r1_tarski(X0_54,u1_struct_0(X1_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK0)))) != iProver_top
% 2.49/1.07      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X2_53) = iProver_top
% 2.49/1.07      | v2_struct_0(sK0) = iProver_top
% 2.49/1.07      | l1_pre_topc(X2_53) != iProver_top
% 2.49/1.07      | l1_pre_topc(sK0) != iProver_top
% 2.49/1.07      | v2_pre_topc(X2_53) != iProver_top
% 2.49/1.07      | v2_pre_topc(sK0) != iProver_top ),
% 2.49/1.07      inference(equality_resolution,[status(thm)],[c_2577]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_4032,plain,
% 2.49/1.07      ( v2_pre_topc(X2_53) != iProver_top
% 2.49/1.07      | v2_struct_0(X2_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.07      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK0)))) != iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/1.07      | r1_tarski(X0_54,u1_struct_0(X1_53)) != iProver_top
% 2.49/1.07      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.49/1.07      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.49/1.07      | r1_tmap_1(X0_53,sK0,sK4,sK7) = iProver_top
% 2.49/1.07      | r1_tmap_1(X1_53,sK0,k3_tmap_1(X2_53,sK0,X0_53,X1_53,sK4),sK7) != iProver_top
% 2.49/1.07      | k1_tops_1(X0_53,X0_54) != sK5
% 2.49/1.07      | u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.49/1.07      | l1_pre_topc(X2_53) != iProver_top ),
% 2.49/1.07      inference(global_propositional_subsumption,
% 2.49/1.07                [status(thm)],
% 2.49/1.07                [c_3473,c_36,c_37,c_38]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_4033,plain,
% 2.49/1.07      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.49/1.07      | k1_tops_1(X0_53,X0_54) != sK5
% 2.49/1.07      | r1_tmap_1(X1_53,sK0,k3_tmap_1(X2_53,sK0,X0_53,X1_53,sK4),sK7) != iProver_top
% 2.49/1.07      | r1_tmap_1(X0_53,sK0,sK4,sK7) = iProver_top
% 2.49/1.07      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.49/1.07      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.49/1.07      | r1_tarski(X0_54,u1_struct_0(X1_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK0)))) != iProver_top
% 2.49/1.07      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X2_53) = iProver_top
% 2.49/1.07      | l1_pre_topc(X2_53) != iProver_top
% 2.49/1.07      | v2_pre_topc(X2_53) != iProver_top ),
% 2.49/1.07      inference(renaming,[status(thm)],[c_4032]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_4052,plain,
% 2.49/1.07      ( k1_tops_1(sK3,X0_54) != sK5
% 2.49/1.07      | r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) != iProver_top
% 2.49/1.07      | r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
% 2.49/1.07      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.49/1.07      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.49/1.07      | r1_tarski(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.49/1.07      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 2.49/1.07      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.07      | v2_struct_0(sK3) = iProver_top
% 2.49/1.07      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.07      | v2_pre_topc(X1_53) != iProver_top ),
% 2.49/1.07      inference(equality_resolution,[status(thm)],[c_4033]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_5235,plain,
% 2.49/1.07      ( v2_struct_0(X0_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.07      | r1_tarski(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.49/1.07      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.49/1.07      | r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
% 2.49/1.07      | r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) != iProver_top
% 2.49/1.07      | k1_tops_1(sK3,X0_54) != sK5
% 2.49/1.07      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.07      | v2_pre_topc(X1_53) != iProver_top ),
% 2.49/1.07      inference(global_propositional_subsumption,
% 2.49/1.07                [status(thm)],
% 2.49/1.07                [c_4052,c_44,c_48,c_2464]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_5236,plain,
% 2.49/1.07      ( k1_tops_1(sK3,X0_54) != sK5
% 2.49/1.07      | r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) != iProver_top
% 2.49/1.07      | r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
% 2.49/1.07      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.49/1.07      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.49/1.07      | r1_tarski(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.07      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.07      | v2_pre_topc(X1_53) != iProver_top ),
% 2.49/1.07      inference(renaming,[status(thm)],[c_5235]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_5253,plain,
% 2.49/1.07      ( r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) != iProver_top
% 2.49/1.07      | r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
% 2.49/1.07      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.49/1.07      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.49/1.07      | r1_tarski(sK5,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.07      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.07      | v2_pre_topc(X1_53) != iProver_top ),
% 2.49/1.07      inference(superposition,[status(thm)],[c_5038,c_5236]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_5841,plain,
% 2.49/1.07      ( r1_tarski(sK5,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.49/1.07      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.49/1.07      | r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
% 2.49/1.07      | r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) != iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.07      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.07      | v2_pre_topc(X1_53) != iProver_top ),
% 2.49/1.07      inference(global_propositional_subsumption,
% 2.49/1.07                [status(thm)],
% 2.49/1.07                [c_5253,c_41,c_49,c_776,c_3261,c_3503]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_5842,plain,
% 2.49/1.07      ( r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) != iProver_top
% 2.49/1.07      | r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
% 2.49/1.07      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.49/1.07      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.49/1.07      | r1_tarski(sK5,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.07      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.07      | v2_pre_topc(X1_53) != iProver_top ),
% 2.49/1.07      inference(renaming,[status(thm)],[c_5841]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_5857,plain,
% 2.49/1.07      ( r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
% 2.49/1.07      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.49/1.07      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.49/1.07      | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
% 2.49/1.07      | v2_struct_0(sK1) = iProver_top
% 2.49/1.07      | v2_struct_0(sK2) = iProver_top
% 2.49/1.07      | l1_pre_topc(sK1) != iProver_top
% 2.49/1.07      | v2_pre_topc(sK1) != iProver_top ),
% 2.49/1.07      inference(superposition,[status(thm)],[c_2499,c_5842]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_5929,plain,
% 2.49/1.07      ( r1_tarski(sK5,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.49/1.07      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.49/1.07      | r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) = iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.07      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.07      | v2_pre_topc(X1_53) != iProver_top ),
% 2.49/1.07      inference(global_propositional_subsumption,
% 2.49/1.07                [status(thm)],
% 2.49/1.07                [c_5276,c_39,c_40,c_41,c_42,c_45,c_49,c_52,c_55,c_776,
% 2.49/1.07                 c_3261,c_3503,c_5857]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_5930,plain,
% 2.49/1.07      ( r1_tmap_1(X0_53,sK0,k3_tmap_1(X1_53,sK0,sK3,X0_53,sK4),sK7) = iProver_top
% 2.49/1.07      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.49/1.07      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.49/1.07      | r1_tarski(sK5,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 2.49/1.07      | v2_struct_0(X1_53) = iProver_top
% 2.49/1.07      | v2_struct_0(X0_53) = iProver_top
% 2.49/1.07      | l1_pre_topc(X1_53) != iProver_top
% 2.49/1.07      | v2_pre_topc(X1_53) != iProver_top ),
% 2.49/1.07      inference(renaming,[status(thm)],[c_5929]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_13,negated_conjecture,
% 2.49/1.07      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.49/1.07      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 2.49/1.07      inference(cnf_transformation,[],[f77]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_1609,negated_conjecture,
% 2.49/1.07      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.49/1.07      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 2.49/1.07      inference(subtyping,[status(esa)],[c_13]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_2413,plain,
% 2.49/1.07      ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
% 2.49/1.07      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
% 2.49/1.07      inference(predicate_to_equality,[status(thm)],[c_1609]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_2504,plain,
% 2.49/1.07      ( r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
% 2.49/1.07      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
% 2.49/1.07      inference(light_normalisation,[status(thm)],[c_2413,c_1607]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(c_5944,plain,
% 2.49/1.07      ( r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
% 2.49/1.07      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.49/1.07      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.49/1.07      | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
% 2.49/1.07      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
% 2.49/1.07      | v2_struct_0(sK1) = iProver_top
% 2.49/1.07      | v2_struct_0(sK2) = iProver_top
% 2.49/1.07      | l1_pre_topc(sK1) != iProver_top
% 2.49/1.07      | v2_pre_topc(sK1) != iProver_top ),
% 2.49/1.07      inference(superposition,[status(thm)],[c_5930,c_2504]) ).
% 2.49/1.07  
% 2.49/1.07  cnf(contradiction,plain,
% 2.49/1.07      ( $false ),
% 2.49/1.07      inference(minisat,
% 2.49/1.07                [status(thm)],
% 2.49/1.07                [c_5944,c_5857,c_55,c_52,c_49,c_45,c_42,c_41,c_40,c_39]) ).
% 2.49/1.07  
% 2.49/1.07  
% 2.49/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 2.49/1.07  
% 2.49/1.07  ------                               Statistics
% 2.49/1.07  
% 2.49/1.07  ------ General
% 2.49/1.07  
% 2.49/1.07  abstr_ref_over_cycles:                  0
% 2.49/1.07  abstr_ref_under_cycles:                 0
% 2.49/1.07  gc_basic_clause_elim:                   0
% 2.49/1.07  forced_gc_time:                         0
% 2.49/1.07  parsing_time:                           0.013
% 2.49/1.07  unif_index_cands_time:                  0.
% 2.49/1.07  unif_index_add_time:                    0.
% 2.49/1.07  orderings_time:                         0.
% 2.49/1.07  out_proof_time:                         0.027
% 2.49/1.07  total_time:                             0.273
% 2.49/1.07  num_of_symbols:                         63
% 2.49/1.07  num_of_terms:                           3106
% 2.49/1.07  
% 2.49/1.07  ------ Preprocessing
% 2.49/1.07  
% 2.49/1.07  num_of_splits:                          4
% 2.49/1.07  num_of_split_atoms:                     4
% 2.49/1.07  num_of_reused_defs:                     0
% 2.49/1.07  num_eq_ax_congr_red:                    22
% 2.49/1.07  num_of_sem_filtered_clauses:            3
% 2.49/1.07  num_of_subtypes:                        3
% 2.49/1.07  monotx_restored_types:                  1
% 2.49/1.07  sat_num_of_epr_types:                   0
% 2.49/1.07  sat_num_of_non_cyclic_types:            0
% 2.49/1.07  sat_guarded_non_collapsed_types:        0
% 2.49/1.07  num_pure_diseq_elim:                    0
% 2.49/1.07  simp_replaced_by:                       0
% 2.49/1.07  res_preprocessed:                       158
% 2.49/1.07  prep_upred:                             0
% 2.49/1.07  prep_unflattend:                        25
% 2.49/1.07  smt_new_axioms:                         0
% 2.49/1.07  pred_elim_cands:                        8
% 2.49/1.07  pred_elim:                              4
% 2.49/1.07  pred_elim_cl:                           5
% 2.49/1.07  pred_elim_cycles:                       6
% 2.49/1.07  merged_defs:                            16
% 2.49/1.07  merged_defs_ncl:                        0
% 2.49/1.07  bin_hyper_res:                          16
% 2.49/1.07  prep_cycles:                            4
% 2.49/1.07  pred_elim_time:                         0.04
% 2.49/1.07  splitting_time:                         0.
% 2.49/1.07  sem_filter_time:                        0.
% 2.49/1.07  monotx_time:                            0.001
% 2.49/1.07  subtype_inf_time:                       0.001
% 2.49/1.07  
% 2.49/1.07  ------ Problem properties
% 2.49/1.07  
% 2.49/1.07  clauses:                                35
% 2.49/1.07  conjectures:                            20
% 2.49/1.07  epr:                                    18
% 2.49/1.07  horn:                                   30
% 2.49/1.07  ground:                                 22
% 2.49/1.07  unary:                                  18
% 2.49/1.07  binary:                                 6
% 2.49/1.07  lits:                                   110
% 2.49/1.07  lits_eq:                                9
% 2.49/1.07  fd_pure:                                0
% 2.49/1.07  fd_pseudo:                              0
% 2.49/1.07  fd_cond:                                0
% 2.49/1.07  fd_pseudo_cond:                         0
% 2.49/1.07  ac_symbols:                             0
% 2.49/1.07  
% 2.49/1.07  ------ Propositional Solver
% 2.49/1.07  
% 2.49/1.07  prop_solver_calls:                      30
% 2.49/1.07  prop_fast_solver_calls:                 1776
% 2.49/1.07  smt_solver_calls:                       0
% 2.49/1.07  smt_fast_solver_calls:                  0
% 2.49/1.07  prop_num_of_clauses:                    1581
% 2.49/1.07  prop_preprocess_simplified:             5231
% 2.49/1.07  prop_fo_subsumed:                       69
% 2.49/1.07  prop_solver_time:                       0.
% 2.49/1.07  smt_solver_time:                        0.
% 2.49/1.07  smt_fast_solver_time:                   0.
% 2.49/1.07  prop_fast_solver_time:                  0.
% 2.49/1.07  prop_unsat_core_time:                   0.
% 2.49/1.07  
% 2.49/1.07  ------ QBF
% 2.49/1.07  
% 2.49/1.07  qbf_q_res:                              0
% 2.49/1.07  qbf_num_tautologies:                    0
% 2.49/1.07  qbf_prep_cycles:                        0
% 2.49/1.07  
% 2.49/1.07  ------ BMC1
% 2.49/1.07  
% 2.49/1.07  bmc1_current_bound:                     -1
% 2.49/1.07  bmc1_last_solved_bound:                 -1
% 2.49/1.07  bmc1_unsat_core_size:                   -1
% 2.49/1.07  bmc1_unsat_core_parents_size:           -1
% 2.49/1.07  bmc1_merge_next_fun:                    0
% 2.49/1.07  bmc1_unsat_core_clauses_time:           0.
% 2.49/1.07  
% 2.49/1.07  ------ Instantiation
% 2.49/1.07  
% 2.49/1.07  inst_num_of_clauses:                    508
% 2.49/1.07  inst_num_in_passive:                    17
% 2.49/1.07  inst_num_in_active:                     356
% 2.49/1.07  inst_num_in_unprocessed:                135
% 2.49/1.07  inst_num_of_loops:                      390
% 2.49/1.07  inst_num_of_learning_restarts:          0
% 2.49/1.07  inst_num_moves_active_passive:          28
% 2.49/1.07  inst_lit_activity:                      0
% 2.49/1.07  inst_lit_activity_moves:                0
% 2.49/1.07  inst_num_tautologies:                   0
% 2.49/1.07  inst_num_prop_implied:                  0
% 2.49/1.07  inst_num_existing_simplified:           0
% 2.49/1.07  inst_num_eq_res_simplified:             0
% 2.49/1.07  inst_num_child_elim:                    0
% 2.49/1.07  inst_num_of_dismatching_blockings:      57
% 2.49/1.07  inst_num_of_non_proper_insts:           544
% 2.49/1.07  inst_num_of_duplicates:                 0
% 2.49/1.07  inst_inst_num_from_inst_to_res:         0
% 2.49/1.07  inst_dismatching_checking_time:         0.
% 2.49/1.07  
% 2.49/1.07  ------ Resolution
% 2.49/1.07  
% 2.49/1.07  res_num_of_clauses:                     0
% 2.49/1.07  res_num_in_passive:                     0
% 2.49/1.07  res_num_in_active:                      0
% 2.49/1.07  res_num_of_loops:                       162
% 2.49/1.07  res_forward_subset_subsumed:            83
% 2.49/1.07  res_backward_subset_subsumed:           2
% 2.49/1.07  res_forward_subsumed:                   0
% 2.49/1.07  res_backward_subsumed:                  0
% 2.49/1.07  res_forward_subsumption_resolution:     6
% 2.49/1.07  res_backward_subsumption_resolution:    0
% 2.49/1.07  res_clause_to_clause_subsumption:       343
% 2.49/1.07  res_orphan_elimination:                 0
% 2.49/1.07  res_tautology_del:                      111
% 2.49/1.07  res_num_eq_res_simplified:              0
% 2.49/1.07  res_num_sel_changes:                    0
% 2.49/1.07  res_moves_from_active_to_pass:          0
% 2.49/1.07  
% 2.49/1.07  ------ Superposition
% 2.49/1.07  
% 2.49/1.07  sup_time_total:                         0.
% 2.49/1.07  sup_time_generating:                    0.
% 2.49/1.07  sup_time_sim_full:                      0.
% 2.49/1.07  sup_time_sim_immed:                     0.
% 2.49/1.07  
% 2.49/1.07  sup_num_of_clauses:                     78
% 2.49/1.07  sup_num_in_active:                      76
% 2.49/1.07  sup_num_in_passive:                     2
% 2.49/1.07  sup_num_of_loops:                       76
% 2.49/1.07  sup_fw_superposition:                   70
% 2.49/1.07  sup_bw_superposition:                   25
% 2.49/1.07  sup_immediate_simplified:               33
% 2.49/1.07  sup_given_eliminated:                   0
% 2.49/1.07  comparisons_done:                       0
% 2.49/1.07  comparisons_avoided:                    0
% 2.49/1.07  
% 2.49/1.07  ------ Simplifications
% 2.49/1.07  
% 2.49/1.07  
% 2.49/1.07  sim_fw_subset_subsumed:                 34
% 2.49/1.07  sim_bw_subset_subsumed:                 1
% 2.49/1.07  sim_fw_subsumed:                        0
% 2.49/1.07  sim_bw_subsumed:                        0
% 2.49/1.07  sim_fw_subsumption_res:                 4
% 2.49/1.07  sim_bw_subsumption_res:                 0
% 2.49/1.07  sim_tautology_del:                      2
% 2.49/1.07  sim_eq_tautology_del:                   0
% 2.49/1.07  sim_eq_res_simp:                        0
% 2.49/1.07  sim_fw_demodulated:                     0
% 2.49/1.07  sim_bw_demodulated:                     0
% 2.49/1.07  sim_light_normalised:                   5
% 2.49/1.07  sim_joinable_taut:                      0
% 2.49/1.07  sim_joinable_simp:                      0
% 2.49/1.07  sim_ac_normalised:                      0
% 2.49/1.07  sim_smt_subsumption:                    0
% 2.49/1.07  
%------------------------------------------------------------------------------
