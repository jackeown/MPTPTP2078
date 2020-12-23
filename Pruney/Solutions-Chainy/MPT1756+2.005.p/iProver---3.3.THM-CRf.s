%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:37 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 903 expanded)
%              Number of clauses        :   96 ( 133 expanded)
%              Number of leaves         :   13 ( 399 expanded)
%              Depth                    :   34
%              Number of atoms          : 1284 (18079 expanded)
%              Number of equality atoms :  165 (1192 expanded)
%              Maximal formula depth    :   27 (   9 average)
%              Maximal clause size      :   44 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
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

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
    inference(nnf_transformation,[],[f14])).

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
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7)
          | ~ r1_tmap_1(X1,X0,X2,X5) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7)
          | r1_tmap_1(X1,X0,X2,X5) )
        & sK7 = X5
        & r1_tarski(X4,u1_struct_0(X3))
        & r2_hidden(X5,X4)
        & v3_pre_topc(X4,X1)
        & m1_subset_1(sK7,u1_struct_0(X3)) ) ) ),
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
              | ~ r1_tmap_1(X1,X0,X2,sK6) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
              | r1_tmap_1(X1,X0,X2,sK6) )
            & sK6 = X6
            & r1_tarski(X4,u1_struct_0(X3))
            & r2_hidden(sK6,X4)
            & v3_pre_topc(X4,X1)
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK6,u1_struct_0(X1)) ) ) ),
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
                & r1_tarski(sK5,u1_struct_0(X3))
                & r2_hidden(X5,sK5)
                & v3_pre_topc(sK5,X1)
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
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
                    ( ( ~ r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X6)
                      | ~ r1_tmap_1(X1,X0,X2,X5) )
                    & ( r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X6)
                      | r1_tmap_1(X1,X0,X2,X5) )
                    & X5 = X6
                    & r1_tarski(X4,u1_struct_0(sK4))
                    & r2_hidden(X5,X4)
                    & v3_pre_topc(X4,X1)
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(sK4,X1)
        & ~ v2_struct_0(sK4) ) ) ),
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
                        ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X6)
                          | ~ r1_tmap_1(X1,X0,sK3,X5) )
                        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X6)
                          | r1_tmap_1(X1,X0,sK3,X5) )
                        & X5 = X6
                        & r1_tarski(X4,u1_struct_0(X3))
                        & r2_hidden(X5,X4)
                        & v3_pre_topc(X4,X1)
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK3) ) ) ),
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
                            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X6)
                              | ~ r1_tmap_1(sK2,X0,X2,X5) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X6)
                              | r1_tmap_1(sK2,X0,X2,X5) )
                            & X5 = X6
                            & r1_tarski(X4,u1_struct_0(X3))
                            & r2_hidden(X5,X4)
                            & v3_pre_topc(X4,sK2)
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,u1_struct_0(sK2)) )
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
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
                              ( ( ~ r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X6)
                                | ~ r1_tmap_1(X1,sK1,X2,X5) )
                              & ( r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X6)
                                | r1_tmap_1(X1,sK1,X2,X5) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7)
      | ~ r1_tmap_1(sK2,sK1,sK3,sK6) )
    & ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7)
      | r1_tmap_1(sK2,sK1,sK3,sK6) )
    & sK6 = sK7
    & r1_tarski(sK5,u1_struct_0(sK4))
    & r2_hidden(sK6,sK5)
    & v3_pre_topc(sK5,sK2)
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f24,f31,f30,f29,f28,f27,f26,f25])).

fof(f56,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
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
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
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
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
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

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ( r2_hidden(X1,sK0(X0,X1,X2))
                & r1_tarski(sK0(X0,X1,X2),X2)
                & v3_pre_topc(sK0(X0,X1,X2),X0)
                & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    v3_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

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
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

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
    inference(nnf_transformation,[],[f12])).

fof(f43,plain,(
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

fof(f68,plain,(
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
    inference(equality_resolution,[],[f43])).

fof(f55,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    r1_tarski(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7)
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7)
    | r1_tmap_1(sK2,sK1,sK3,sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
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

fof(f67,plain,(
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
    inference(equality_resolution,[],[f44])).

fof(f60,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3155,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X3,k1_tops_1(X1,X2))
    | ~ r1_tarski(X0,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1101,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X3,k1_tops_1(X1,X2))
    | ~ r1_tarski(X0,X2)
    | ~ v2_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_26])).

cnf(c_1102,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(X1,sK2)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(X2,k1_tops_1(sK2,X0))
    | ~ r1_tarski(X1,X0)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1101])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1106,plain,
    ( ~ r1_tarski(X1,X0)
    | r2_hidden(X2,k1_tops_1(sK2,X0))
    | ~ r2_hidden(X2,X1)
    | ~ v3_pre_topc(X1,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1102,c_27])).

cnf(c_1107,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(X1,sK2)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(X2,k1_tops_1(sK2,X0))
    | ~ r1_tarski(X1,X0) ),
    inference(renaming,[status(thm)],[c_1106])).

cnf(c_3145,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_pre_topc(X1,sK2) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,k1_tops_1(sK2,X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1107])).

cnf(c_4915,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_pre_topc(X0,sK2) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,sK5)) = iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_3145])).

cnf(c_5029,plain,
    ( v3_pre_topc(sK5,sK2) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK5)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_4915])).

cnf(c_17,negated_conjecture,
    ( v3_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_46,plain,
    ( v3_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3768,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3771,plain,
    ( r1_tarski(sK5,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3768])).

cnf(c_5058,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5029,c_46,c_3771])).

cnf(c_5059,plain,
    ( r2_hidden(X0,k1_tops_1(sK2,sK5)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_5058])).

cnf(c_8,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f68])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_452,plain,
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
    | sK2 != X0
    | sK4 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_453,plain,
    ( ~ r1_tmap_1(sK2,X0,X1,X2)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r1_tarski(X3,u1_struct_0(sK4))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_457,plain,
    ( ~ l1_pre_topc(X0)
    | ~ r1_tmap_1(sK2,X0,X1,X2)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r1_tarski(X3,u1_struct_0(sK4))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_453,c_28,c_27,c_26,c_22])).

cnf(c_458,plain,
    ( ~ r1_tmap_1(sK2,X0,X1,X2)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r1_tarski(X3,u1_struct_0(sK4))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_457])).

cnf(c_604,plain,
    ( ~ r1_tmap_1(sK2,X0,X1,X2)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
    | ~ m1_connsp_2(X3,sK2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r1_tarski(X3,u1_struct_0(sK4))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_458])).

cnf(c_605,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_connsp_2(X2,sK2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ v1_funct_1(sK3)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_609,plain,
    ( ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_connsp_2(X2,sK2,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ r1_tmap_1(sK2,X0,sK3,X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_605,c_25])).

cnf(c_610,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_connsp_2(X2,sK2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_609])).

cnf(c_655,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r2_hidden(X5,k1_tops_1(X3,X2))
    | ~ r1_tarski(X4,u1_struct_0(sK4))
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X0)
    | X4 != X2
    | X1 != X5
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_610])).

cnf(c_656,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_660,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ r1_tmap_1(sK2,X0,sK3,X1)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_656,c_28,c_27,c_26])).

cnf(c_661,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_660])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_941,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_661,c_31])).

cnf(c_942,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_941])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_946,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_942,c_30,c_29,c_23])).

cnf(c_947,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_946])).

cnf(c_1944,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
    | ~ r1_tarski(X1,u1_struct_0(sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_947])).

cnf(c_3131,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,X1)) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1944])).

cnf(c_4036,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK5)) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_3131])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_48,plain,
    ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4193,plain,
    ( r2_hidden(X0,k1_tops_1(sK2,sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0) = iProver_top
    | r1_tmap_1(sK2,sK1,sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4036,c_48])).

cnf(c_4194,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4193])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3162,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3196,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK7) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3162,c_14])).

cnf(c_4204,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK7,k1_tops_1(sK2,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4194,c_3196])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_45,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3156,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3174,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3156,c_14])).

cnf(c_13,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,sK3,sK6)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3161,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3191,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK7) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3161,c_14])).

cnf(c_10,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_503,plain,
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
    | sK2 != X0
    | sK4 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_504,plain,
    ( r1_tmap_1(sK2,X0,X1,X2)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r1_tarski(X3,u1_struct_0(sK4))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_508,plain,
    ( ~ l1_pre_topc(X0)
    | r1_tmap_1(sK2,X0,X1,X2)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r1_tarski(X3,u1_struct_0(sK4))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_504,c_28,c_27,c_26,c_22])).

cnf(c_509,plain,
    ( r1_tmap_1(sK2,X0,X1,X2)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r1_tarski(X3,u1_struct_0(sK4))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_508])).

cnf(c_556,plain,
    ( r1_tmap_1(sK2,X0,X1,X2)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
    | ~ m1_connsp_2(X3,sK2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r1_tarski(X3,u1_struct_0(sK4))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_509])).

cnf(c_557,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_connsp_2(X2,sK2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ v1_funct_1(sK3)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_561,plain,
    ( ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_connsp_2(X2,sK2,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | r1_tmap_1(sK2,X0,sK3,X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_557,c_25])).

cnf(c_562,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_connsp_2(X2,sK2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_561])).

cnf(c_701,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r2_hidden(X5,k1_tops_1(X3,X2))
    | ~ r1_tarski(X4,u1_struct_0(sK4))
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X0)
    | X4 != X2
    | X1 != X5
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_562])).

cnf(c_702,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_701])).

cnf(c_706,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | r1_tmap_1(sK2,X0,sK3,X1)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_702,c_28,c_27,c_26])).

cnf(c_707,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_706])).

cnf(c_905,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_707,c_31])).

cnf(c_906,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_905])).

cnf(c_910,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_906,c_30,c_29,c_23])).

cnf(c_911,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_910])).

cnf(c_1948,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
    | ~ r1_tarski(X1,u1_struct_0(sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_911])).

cnf(c_3130,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,X1)) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1948])).

cnf(c_3713,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK7,k1_tops_1(sK2,X0)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3191,c_3130])).

cnf(c_4118,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK7,k1_tops_1(sK2,X0)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3713,c_45,c_3174])).

cnf(c_4128,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK7) = iProver_top
    | r2_hidden(sK7,k1_tops_1(sK2,sK5)) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_4118])).

cnf(c_4131,plain,
    ( r2_hidden(sK7,k1_tops_1(sK2,sK5)) != iProver_top
    | r1_tmap_1(sK2,sK1,sK3,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4128,c_48])).

cnf(c_4132,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK7) = iProver_top
    | r2_hidden(sK7,k1_tops_1(sK2,sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4131])).

cnf(c_4711,plain,
    ( r2_hidden(sK7,k1_tops_1(sK2,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4204,c_45,c_3174,c_4132])).

cnf(c_5066,plain,
    ( r2_hidden(sK7,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5059,c_4711])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3159,plain,
    ( r2_hidden(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3169,plain,
    ( r2_hidden(sK7,sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3159,c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5066,c_3169])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:24:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.84/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.02  
% 1.84/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.84/1.02  
% 1.84/1.02  ------  iProver source info
% 1.84/1.02  
% 1.84/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.84/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.84/1.02  git: non_committed_changes: false
% 1.84/1.02  git: last_make_outside_of_git: false
% 1.84/1.02  
% 1.84/1.02  ------ 
% 1.84/1.02  
% 1.84/1.02  ------ Input Options
% 1.84/1.02  
% 1.84/1.02  --out_options                           all
% 1.84/1.02  --tptp_safe_out                         true
% 1.84/1.02  --problem_path                          ""
% 1.84/1.02  --include_path                          ""
% 1.84/1.02  --clausifier                            res/vclausify_rel
% 1.84/1.02  --clausifier_options                    --mode clausify
% 1.84/1.02  --stdin                                 false
% 1.84/1.02  --stats_out                             all
% 1.84/1.02  
% 1.84/1.02  ------ General Options
% 1.84/1.02  
% 1.84/1.02  --fof                                   false
% 1.84/1.02  --time_out_real                         305.
% 1.84/1.02  --time_out_virtual                      -1.
% 1.84/1.02  --symbol_type_check                     false
% 1.84/1.02  --clausify_out                          false
% 1.84/1.02  --sig_cnt_out                           false
% 1.84/1.02  --trig_cnt_out                          false
% 1.84/1.02  --trig_cnt_out_tolerance                1.
% 1.84/1.02  --trig_cnt_out_sk_spl                   false
% 1.84/1.02  --abstr_cl_out                          false
% 1.84/1.02  
% 1.84/1.02  ------ Global Options
% 1.84/1.02  
% 1.84/1.02  --schedule                              default
% 1.84/1.02  --add_important_lit                     false
% 1.84/1.02  --prop_solver_per_cl                    1000
% 1.84/1.02  --min_unsat_core                        false
% 1.84/1.02  --soft_assumptions                      false
% 1.84/1.02  --soft_lemma_size                       3
% 1.84/1.02  --prop_impl_unit_size                   0
% 1.84/1.02  --prop_impl_unit                        []
% 1.84/1.02  --share_sel_clauses                     true
% 1.84/1.02  --reset_solvers                         false
% 1.84/1.02  --bc_imp_inh                            [conj_cone]
% 1.84/1.02  --conj_cone_tolerance                   3.
% 1.84/1.02  --extra_neg_conj                        none
% 1.84/1.02  --large_theory_mode                     true
% 1.84/1.02  --prolific_symb_bound                   200
% 1.84/1.02  --lt_threshold                          2000
% 1.84/1.02  --clause_weak_htbl                      true
% 1.84/1.02  --gc_record_bc_elim                     false
% 1.84/1.02  
% 1.84/1.02  ------ Preprocessing Options
% 1.84/1.02  
% 1.84/1.02  --preprocessing_flag                    true
% 1.84/1.02  --time_out_prep_mult                    0.1
% 1.84/1.02  --splitting_mode                        input
% 1.84/1.02  --splitting_grd                         true
% 1.84/1.02  --splitting_cvd                         false
% 1.84/1.02  --splitting_cvd_svl                     false
% 1.84/1.02  --splitting_nvd                         32
% 1.84/1.02  --sub_typing                            true
% 1.84/1.02  --prep_gs_sim                           true
% 1.84/1.02  --prep_unflatten                        true
% 1.84/1.02  --prep_res_sim                          true
% 1.84/1.02  --prep_upred                            true
% 1.84/1.02  --prep_sem_filter                       exhaustive
% 1.84/1.02  --prep_sem_filter_out                   false
% 1.84/1.02  --pred_elim                             true
% 1.84/1.02  --res_sim_input                         true
% 1.84/1.02  --eq_ax_congr_red                       true
% 1.84/1.02  --pure_diseq_elim                       true
% 1.84/1.02  --brand_transform                       false
% 1.84/1.02  --non_eq_to_eq                          false
% 1.84/1.02  --prep_def_merge                        true
% 1.84/1.02  --prep_def_merge_prop_impl              false
% 1.84/1.02  --prep_def_merge_mbd                    true
% 1.84/1.02  --prep_def_merge_tr_red                 false
% 1.84/1.02  --prep_def_merge_tr_cl                  false
% 1.84/1.02  --smt_preprocessing                     true
% 1.84/1.02  --smt_ac_axioms                         fast
% 1.84/1.02  --preprocessed_out                      false
% 1.84/1.02  --preprocessed_stats                    false
% 1.84/1.02  
% 1.84/1.02  ------ Abstraction refinement Options
% 1.84/1.02  
% 1.84/1.02  --abstr_ref                             []
% 1.84/1.02  --abstr_ref_prep                        false
% 1.84/1.02  --abstr_ref_until_sat                   false
% 1.84/1.02  --abstr_ref_sig_restrict                funpre
% 1.84/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.84/1.02  --abstr_ref_under                       []
% 1.84/1.02  
% 1.84/1.02  ------ SAT Options
% 1.84/1.02  
% 1.84/1.02  --sat_mode                              false
% 1.84/1.02  --sat_fm_restart_options                ""
% 1.84/1.02  --sat_gr_def                            false
% 1.84/1.02  --sat_epr_types                         true
% 1.84/1.02  --sat_non_cyclic_types                  false
% 1.84/1.02  --sat_finite_models                     false
% 1.84/1.02  --sat_fm_lemmas                         false
% 1.84/1.02  --sat_fm_prep                           false
% 1.84/1.02  --sat_fm_uc_incr                        true
% 1.84/1.02  --sat_out_model                         small
% 1.84/1.02  --sat_out_clauses                       false
% 1.84/1.02  
% 1.84/1.02  ------ QBF Options
% 1.84/1.02  
% 1.84/1.02  --qbf_mode                              false
% 1.84/1.02  --qbf_elim_univ                         false
% 1.84/1.02  --qbf_dom_inst                          none
% 1.84/1.02  --qbf_dom_pre_inst                      false
% 1.84/1.02  --qbf_sk_in                             false
% 1.84/1.02  --qbf_pred_elim                         true
% 1.84/1.02  --qbf_split                             512
% 1.84/1.02  
% 1.84/1.02  ------ BMC1 Options
% 1.84/1.02  
% 1.84/1.02  --bmc1_incremental                      false
% 1.84/1.02  --bmc1_axioms                           reachable_all
% 1.84/1.02  --bmc1_min_bound                        0
% 1.84/1.02  --bmc1_max_bound                        -1
% 1.84/1.02  --bmc1_max_bound_default                -1
% 1.84/1.02  --bmc1_symbol_reachability              true
% 1.84/1.02  --bmc1_property_lemmas                  false
% 1.84/1.02  --bmc1_k_induction                      false
% 1.84/1.02  --bmc1_non_equiv_states                 false
% 1.84/1.02  --bmc1_deadlock                         false
% 1.84/1.02  --bmc1_ucm                              false
% 1.84/1.02  --bmc1_add_unsat_core                   none
% 1.84/1.02  --bmc1_unsat_core_children              false
% 1.84/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.84/1.02  --bmc1_out_stat                         full
% 1.84/1.02  --bmc1_ground_init                      false
% 1.84/1.02  --bmc1_pre_inst_next_state              false
% 1.84/1.02  --bmc1_pre_inst_state                   false
% 1.84/1.02  --bmc1_pre_inst_reach_state             false
% 1.84/1.02  --bmc1_out_unsat_core                   false
% 1.84/1.02  --bmc1_aig_witness_out                  false
% 1.84/1.02  --bmc1_verbose                          false
% 1.84/1.02  --bmc1_dump_clauses_tptp                false
% 1.84/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.84/1.02  --bmc1_dump_file                        -
% 1.84/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.84/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.84/1.02  --bmc1_ucm_extend_mode                  1
% 1.84/1.02  --bmc1_ucm_init_mode                    2
% 1.84/1.02  --bmc1_ucm_cone_mode                    none
% 1.84/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.84/1.02  --bmc1_ucm_relax_model                  4
% 1.84/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.84/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.84/1.02  --bmc1_ucm_layered_model                none
% 1.84/1.02  --bmc1_ucm_max_lemma_size               10
% 1.84/1.02  
% 1.84/1.02  ------ AIG Options
% 1.84/1.02  
% 1.84/1.02  --aig_mode                              false
% 1.84/1.02  
% 1.84/1.02  ------ Instantiation Options
% 1.84/1.02  
% 1.84/1.02  --instantiation_flag                    true
% 1.84/1.02  --inst_sos_flag                         false
% 1.84/1.02  --inst_sos_phase                        true
% 1.84/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.84/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.84/1.02  --inst_lit_sel_side                     num_symb
% 1.84/1.02  --inst_solver_per_active                1400
% 1.84/1.02  --inst_solver_calls_frac                1.
% 1.84/1.02  --inst_passive_queue_type               priority_queues
% 1.84/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.84/1.02  --inst_passive_queues_freq              [25;2]
% 1.84/1.02  --inst_dismatching                      true
% 1.84/1.02  --inst_eager_unprocessed_to_passive     true
% 1.84/1.02  --inst_prop_sim_given                   true
% 1.84/1.02  --inst_prop_sim_new                     false
% 1.84/1.02  --inst_subs_new                         false
% 1.84/1.02  --inst_eq_res_simp                      false
% 1.84/1.02  --inst_subs_given                       false
% 1.84/1.02  --inst_orphan_elimination               true
% 1.84/1.02  --inst_learning_loop_flag               true
% 1.84/1.02  --inst_learning_start                   3000
% 1.84/1.02  --inst_learning_factor                  2
% 1.84/1.02  --inst_start_prop_sim_after_learn       3
% 1.84/1.02  --inst_sel_renew                        solver
% 1.84/1.02  --inst_lit_activity_flag                true
% 1.84/1.02  --inst_restr_to_given                   false
% 1.84/1.02  --inst_activity_threshold               500
% 1.84/1.02  --inst_out_proof                        true
% 1.84/1.02  
% 1.84/1.02  ------ Resolution Options
% 1.84/1.02  
% 1.84/1.02  --resolution_flag                       true
% 1.84/1.02  --res_lit_sel                           adaptive
% 1.84/1.02  --res_lit_sel_side                      none
% 1.84/1.02  --res_ordering                          kbo
% 1.84/1.02  --res_to_prop_solver                    active
% 1.84/1.02  --res_prop_simpl_new                    false
% 1.84/1.02  --res_prop_simpl_given                  true
% 1.84/1.02  --res_passive_queue_type                priority_queues
% 1.84/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.84/1.02  --res_passive_queues_freq               [15;5]
% 1.84/1.02  --res_forward_subs                      full
% 1.84/1.02  --res_backward_subs                     full
% 1.84/1.02  --res_forward_subs_resolution           true
% 1.84/1.02  --res_backward_subs_resolution          true
% 1.84/1.02  --res_orphan_elimination                true
% 1.84/1.02  --res_time_limit                        2.
% 1.84/1.02  --res_out_proof                         true
% 1.84/1.02  
% 1.84/1.02  ------ Superposition Options
% 1.84/1.02  
% 1.84/1.02  --superposition_flag                    true
% 1.84/1.02  --sup_passive_queue_type                priority_queues
% 1.84/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.84/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.84/1.02  --demod_completeness_check              fast
% 1.84/1.02  --demod_use_ground                      true
% 1.84/1.02  --sup_to_prop_solver                    passive
% 1.84/1.02  --sup_prop_simpl_new                    true
% 1.84/1.02  --sup_prop_simpl_given                  true
% 1.84/1.02  --sup_fun_splitting                     false
% 1.84/1.02  --sup_smt_interval                      50000
% 1.84/1.02  
% 1.84/1.02  ------ Superposition Simplification Setup
% 1.84/1.02  
% 1.84/1.02  --sup_indices_passive                   []
% 1.84/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.84/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/1.02  --sup_full_bw                           [BwDemod]
% 1.84/1.02  --sup_immed_triv                        [TrivRules]
% 1.84/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.84/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/1.02  --sup_immed_bw_main                     []
% 1.84/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.84/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/1.02  
% 1.84/1.02  ------ Combination Options
% 1.84/1.02  
% 1.84/1.02  --comb_res_mult                         3
% 1.84/1.02  --comb_sup_mult                         2
% 1.84/1.02  --comb_inst_mult                        10
% 1.84/1.02  
% 1.84/1.02  ------ Debug Options
% 1.84/1.02  
% 1.84/1.02  --dbg_backtrace                         false
% 1.84/1.02  --dbg_dump_prop_clauses                 false
% 1.84/1.02  --dbg_dump_prop_clauses_file            -
% 1.84/1.02  --dbg_out_stat                          false
% 1.84/1.02  ------ Parsing...
% 1.84/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.84/1.02  
% 1.84/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.84/1.02  
% 1.84/1.02  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.84/1.02  
% 1.84/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.84/1.02  ------ Proving...
% 1.84/1.02  ------ Problem Properties 
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  clauses                                 36
% 1.84/1.02  conjectures                             10
% 1.84/1.02  EPR                                     5
% 1.84/1.02  Horn                                    35
% 1.84/1.02  unary                                   9
% 1.84/1.02  binary                                  2
% 1.84/1.02  lits                                    136
% 1.84/1.02  lits eq                                 12
% 1.84/1.02  fd_pure                                 0
% 1.84/1.02  fd_pseudo                               0
% 1.84/1.02  fd_cond                                 0
% 1.84/1.02  fd_pseudo_cond                          1
% 1.84/1.02  AC symbols                              0
% 1.84/1.02  
% 1.84/1.02  ------ Schedule dynamic 5 is on 
% 1.84/1.02  
% 1.84/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  ------ 
% 1.84/1.02  Current options:
% 1.84/1.02  ------ 
% 1.84/1.02  
% 1.84/1.02  ------ Input Options
% 1.84/1.02  
% 1.84/1.02  --out_options                           all
% 1.84/1.02  --tptp_safe_out                         true
% 1.84/1.02  --problem_path                          ""
% 1.84/1.02  --include_path                          ""
% 1.84/1.02  --clausifier                            res/vclausify_rel
% 1.84/1.02  --clausifier_options                    --mode clausify
% 1.84/1.02  --stdin                                 false
% 1.84/1.02  --stats_out                             all
% 1.84/1.02  
% 1.84/1.02  ------ General Options
% 1.84/1.02  
% 1.84/1.02  --fof                                   false
% 1.84/1.02  --time_out_real                         305.
% 1.84/1.02  --time_out_virtual                      -1.
% 1.84/1.02  --symbol_type_check                     false
% 1.84/1.02  --clausify_out                          false
% 1.84/1.02  --sig_cnt_out                           false
% 1.84/1.02  --trig_cnt_out                          false
% 1.84/1.02  --trig_cnt_out_tolerance                1.
% 1.84/1.02  --trig_cnt_out_sk_spl                   false
% 1.84/1.02  --abstr_cl_out                          false
% 1.84/1.02  
% 1.84/1.02  ------ Global Options
% 1.84/1.02  
% 1.84/1.02  --schedule                              default
% 1.84/1.02  --add_important_lit                     false
% 1.84/1.02  --prop_solver_per_cl                    1000
% 1.84/1.02  --min_unsat_core                        false
% 1.84/1.02  --soft_assumptions                      false
% 1.84/1.02  --soft_lemma_size                       3
% 1.84/1.02  --prop_impl_unit_size                   0
% 1.84/1.02  --prop_impl_unit                        []
% 1.84/1.02  --share_sel_clauses                     true
% 1.84/1.02  --reset_solvers                         false
% 1.84/1.02  --bc_imp_inh                            [conj_cone]
% 1.84/1.02  --conj_cone_tolerance                   3.
% 1.84/1.02  --extra_neg_conj                        none
% 1.84/1.02  --large_theory_mode                     true
% 1.84/1.02  --prolific_symb_bound                   200
% 1.84/1.02  --lt_threshold                          2000
% 1.84/1.02  --clause_weak_htbl                      true
% 1.84/1.02  --gc_record_bc_elim                     false
% 1.84/1.02  
% 1.84/1.02  ------ Preprocessing Options
% 1.84/1.02  
% 1.84/1.02  --preprocessing_flag                    true
% 1.84/1.02  --time_out_prep_mult                    0.1
% 1.84/1.02  --splitting_mode                        input
% 1.84/1.02  --splitting_grd                         true
% 1.84/1.02  --splitting_cvd                         false
% 1.84/1.02  --splitting_cvd_svl                     false
% 1.84/1.02  --splitting_nvd                         32
% 1.84/1.02  --sub_typing                            true
% 1.84/1.02  --prep_gs_sim                           true
% 1.84/1.02  --prep_unflatten                        true
% 1.84/1.02  --prep_res_sim                          true
% 1.84/1.02  --prep_upred                            true
% 1.84/1.02  --prep_sem_filter                       exhaustive
% 1.84/1.02  --prep_sem_filter_out                   false
% 1.84/1.02  --pred_elim                             true
% 1.84/1.02  --res_sim_input                         true
% 1.84/1.02  --eq_ax_congr_red                       true
% 1.84/1.02  --pure_diseq_elim                       true
% 1.84/1.02  --brand_transform                       false
% 1.84/1.02  --non_eq_to_eq                          false
% 1.84/1.02  --prep_def_merge                        true
% 1.84/1.02  --prep_def_merge_prop_impl              false
% 1.84/1.02  --prep_def_merge_mbd                    true
% 1.84/1.02  --prep_def_merge_tr_red                 false
% 1.84/1.02  --prep_def_merge_tr_cl                  false
% 1.84/1.02  --smt_preprocessing                     true
% 1.84/1.02  --smt_ac_axioms                         fast
% 1.84/1.02  --preprocessed_out                      false
% 1.84/1.02  --preprocessed_stats                    false
% 1.84/1.02  
% 1.84/1.02  ------ Abstraction refinement Options
% 1.84/1.02  
% 1.84/1.02  --abstr_ref                             []
% 1.84/1.02  --abstr_ref_prep                        false
% 1.84/1.02  --abstr_ref_until_sat                   false
% 1.84/1.02  --abstr_ref_sig_restrict                funpre
% 1.84/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.84/1.02  --abstr_ref_under                       []
% 1.84/1.02  
% 1.84/1.02  ------ SAT Options
% 1.84/1.02  
% 1.84/1.02  --sat_mode                              false
% 1.84/1.02  --sat_fm_restart_options                ""
% 1.84/1.02  --sat_gr_def                            false
% 1.84/1.02  --sat_epr_types                         true
% 1.84/1.02  --sat_non_cyclic_types                  false
% 1.84/1.02  --sat_finite_models                     false
% 1.84/1.02  --sat_fm_lemmas                         false
% 1.84/1.02  --sat_fm_prep                           false
% 1.84/1.02  --sat_fm_uc_incr                        true
% 1.84/1.02  --sat_out_model                         small
% 1.84/1.02  --sat_out_clauses                       false
% 1.84/1.02  
% 1.84/1.02  ------ QBF Options
% 1.84/1.02  
% 1.84/1.02  --qbf_mode                              false
% 1.84/1.02  --qbf_elim_univ                         false
% 1.84/1.02  --qbf_dom_inst                          none
% 1.84/1.02  --qbf_dom_pre_inst                      false
% 1.84/1.02  --qbf_sk_in                             false
% 1.84/1.02  --qbf_pred_elim                         true
% 1.84/1.02  --qbf_split                             512
% 1.84/1.02  
% 1.84/1.02  ------ BMC1 Options
% 1.84/1.02  
% 1.84/1.02  --bmc1_incremental                      false
% 1.84/1.02  --bmc1_axioms                           reachable_all
% 1.84/1.02  --bmc1_min_bound                        0
% 1.84/1.02  --bmc1_max_bound                        -1
% 1.84/1.02  --bmc1_max_bound_default                -1
% 1.84/1.02  --bmc1_symbol_reachability              true
% 1.84/1.02  --bmc1_property_lemmas                  false
% 1.84/1.02  --bmc1_k_induction                      false
% 1.84/1.02  --bmc1_non_equiv_states                 false
% 1.84/1.02  --bmc1_deadlock                         false
% 1.84/1.02  --bmc1_ucm                              false
% 1.84/1.02  --bmc1_add_unsat_core                   none
% 1.84/1.02  --bmc1_unsat_core_children              false
% 1.84/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.84/1.02  --bmc1_out_stat                         full
% 1.84/1.02  --bmc1_ground_init                      false
% 1.84/1.02  --bmc1_pre_inst_next_state              false
% 1.84/1.02  --bmc1_pre_inst_state                   false
% 1.84/1.02  --bmc1_pre_inst_reach_state             false
% 1.84/1.02  --bmc1_out_unsat_core                   false
% 1.84/1.02  --bmc1_aig_witness_out                  false
% 1.84/1.02  --bmc1_verbose                          false
% 1.84/1.02  --bmc1_dump_clauses_tptp                false
% 1.84/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.84/1.02  --bmc1_dump_file                        -
% 1.84/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.84/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.84/1.02  --bmc1_ucm_extend_mode                  1
% 1.84/1.02  --bmc1_ucm_init_mode                    2
% 1.84/1.02  --bmc1_ucm_cone_mode                    none
% 1.84/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.84/1.02  --bmc1_ucm_relax_model                  4
% 1.84/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.84/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.84/1.02  --bmc1_ucm_layered_model                none
% 1.84/1.02  --bmc1_ucm_max_lemma_size               10
% 1.84/1.02  
% 1.84/1.02  ------ AIG Options
% 1.84/1.02  
% 1.84/1.02  --aig_mode                              false
% 1.84/1.02  
% 1.84/1.02  ------ Instantiation Options
% 1.84/1.02  
% 1.84/1.02  --instantiation_flag                    true
% 1.84/1.02  --inst_sos_flag                         false
% 1.84/1.02  --inst_sos_phase                        true
% 1.84/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.84/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.84/1.02  --inst_lit_sel_side                     none
% 1.84/1.02  --inst_solver_per_active                1400
% 1.84/1.02  --inst_solver_calls_frac                1.
% 1.84/1.02  --inst_passive_queue_type               priority_queues
% 1.84/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.84/1.02  --inst_passive_queues_freq              [25;2]
% 1.84/1.02  --inst_dismatching                      true
% 1.84/1.02  --inst_eager_unprocessed_to_passive     true
% 1.84/1.02  --inst_prop_sim_given                   true
% 1.84/1.02  --inst_prop_sim_new                     false
% 1.84/1.02  --inst_subs_new                         false
% 1.84/1.02  --inst_eq_res_simp                      false
% 1.84/1.02  --inst_subs_given                       false
% 1.84/1.02  --inst_orphan_elimination               true
% 1.84/1.02  --inst_learning_loop_flag               true
% 1.84/1.02  --inst_learning_start                   3000
% 1.84/1.02  --inst_learning_factor                  2
% 1.84/1.02  --inst_start_prop_sim_after_learn       3
% 1.84/1.02  --inst_sel_renew                        solver
% 1.84/1.02  --inst_lit_activity_flag                true
% 1.84/1.02  --inst_restr_to_given                   false
% 1.84/1.02  --inst_activity_threshold               500
% 1.84/1.02  --inst_out_proof                        true
% 1.84/1.02  
% 1.84/1.02  ------ Resolution Options
% 1.84/1.02  
% 1.84/1.02  --resolution_flag                       false
% 1.84/1.02  --res_lit_sel                           adaptive
% 1.84/1.02  --res_lit_sel_side                      none
% 1.84/1.02  --res_ordering                          kbo
% 1.84/1.02  --res_to_prop_solver                    active
% 1.84/1.02  --res_prop_simpl_new                    false
% 1.84/1.02  --res_prop_simpl_given                  true
% 1.84/1.02  --res_passive_queue_type                priority_queues
% 1.84/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.84/1.02  --res_passive_queues_freq               [15;5]
% 1.84/1.02  --res_forward_subs                      full
% 1.84/1.02  --res_backward_subs                     full
% 1.84/1.02  --res_forward_subs_resolution           true
% 1.84/1.02  --res_backward_subs_resolution          true
% 1.84/1.02  --res_orphan_elimination                true
% 1.84/1.02  --res_time_limit                        2.
% 1.84/1.02  --res_out_proof                         true
% 1.84/1.02  
% 1.84/1.02  ------ Superposition Options
% 1.84/1.02  
% 1.84/1.02  --superposition_flag                    true
% 1.84/1.02  --sup_passive_queue_type                priority_queues
% 1.84/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.84/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.84/1.02  --demod_completeness_check              fast
% 1.84/1.02  --demod_use_ground                      true
% 1.84/1.02  --sup_to_prop_solver                    passive
% 1.84/1.02  --sup_prop_simpl_new                    true
% 1.84/1.02  --sup_prop_simpl_given                  true
% 1.84/1.02  --sup_fun_splitting                     false
% 1.84/1.02  --sup_smt_interval                      50000
% 1.84/1.02  
% 1.84/1.02  ------ Superposition Simplification Setup
% 1.84/1.02  
% 1.84/1.02  --sup_indices_passive                   []
% 1.84/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.84/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/1.02  --sup_full_bw                           [BwDemod]
% 1.84/1.02  --sup_immed_triv                        [TrivRules]
% 1.84/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.84/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/1.02  --sup_immed_bw_main                     []
% 1.84/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.84/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/1.02  
% 1.84/1.02  ------ Combination Options
% 1.84/1.02  
% 1.84/1.02  --comb_res_mult                         3
% 1.84/1.02  --comb_sup_mult                         2
% 1.84/1.02  --comb_inst_mult                        10
% 1.84/1.02  
% 1.84/1.02  ------ Debug Options
% 1.84/1.02  
% 1.84/1.02  --dbg_backtrace                         false
% 1.84/1.02  --dbg_dump_prop_clauses                 false
% 1.84/1.02  --dbg_dump_prop_clauses_file            -
% 1.84/1.02  --dbg_out_stat                          false
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  ------ Proving...
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  % SZS status Theorem for theBenchmark.p
% 1.84/1.02  
% 1.84/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.84/1.02  
% 1.84/1.02  fof(f5,conjecture,(
% 1.84/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f6,negated_conjecture,(
% 1.84/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.84/1.02    inference(negated_conjecture,[],[f5])).
% 1.84/1.02  
% 1.84/1.02  fof(f13,plain,(
% 1.84/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.84/1.02    inference(ennf_transformation,[],[f6])).
% 1.84/1.02  
% 1.84/1.02  fof(f14,plain,(
% 1.84/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.84/1.02    inference(flattening,[],[f13])).
% 1.84/1.02  
% 1.84/1.02  fof(f23,plain,(
% 1.84/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5))) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.84/1.02    inference(nnf_transformation,[],[f14])).
% 1.84/1.02  
% 1.84/1.02  fof(f24,plain,(
% 1.84/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.84/1.02    inference(flattening,[],[f23])).
% 1.84/1.02  
% 1.84/1.02  fof(f31,plain,(
% 1.84/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7) | r1_tmap_1(X1,X0,X2,X5)) & sK7 = X5 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 1.84/1.02    introduced(choice_axiom,[])).
% 1.84/1.02  
% 1.84/1.02  fof(f30,plain,(
% 1.84/1.02    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,sK6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,sK6)) & sK6 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(sK6,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK6,u1_struct_0(X1)))) )),
% 1.84/1.02    introduced(choice_axiom,[])).
% 1.84/1.02  
% 1.84/1.02  fof(f29,plain,(
% 1.84/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(sK5,u1_struct_0(X3)) & r2_hidden(X5,sK5) & v3_pre_topc(sK5,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 1.84/1.02    introduced(choice_axiom,[])).
% 1.84/1.02  
% 1.84/1.02  fof(f28,plain,(
% 1.84/1.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(sK4)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK4,X1) & ~v2_struct_0(sK4))) )),
% 1.84/1.02    introduced(choice_axiom,[])).
% 1.84/1.02  
% 1.84/1.02  fof(f27,plain,(
% 1.84/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X6) | ~r1_tmap_1(X1,X0,sK3,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X6) | r1_tmap_1(X1,X0,sK3,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 1.84/1.02    introduced(choice_axiom,[])).
% 1.84/1.02  
% 1.84/1.02  fof(f26,plain,(
% 1.84/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X6) | ~r1_tmap_1(sK2,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X6) | r1_tmap_1(sK2,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK2) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 1.84/1.02    introduced(choice_axiom,[])).
% 1.84/1.02  
% 1.84/1.02  fof(f25,plain,(
% 1.84/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X6) | ~r1_tmap_1(X1,sK1,X2,X5)) & (r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X6) | r1_tmap_1(X1,sK1,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.84/1.02    introduced(choice_axiom,[])).
% 1.84/1.02  
% 1.84/1.02  fof(f32,plain,(
% 1.84/1.02    (((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7) | ~r1_tmap_1(sK2,sK1,sK3,sK6)) & (r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7) | r1_tmap_1(sK2,sK1,sK3,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK4)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK2) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.84/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f24,f31,f30,f29,f28,f27,f26,f25])).
% 1.84/1.02  
% 1.84/1.02  fof(f56,plain,(
% 1.84/1.02    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f2,axiom,(
% 1.84/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f7,plain,(
% 1.84/1.02    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.84/1.02    inference(ennf_transformation,[],[f2])).
% 1.84/1.02  
% 1.84/1.02  fof(f8,plain,(
% 1.84/1.02    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.84/1.02    inference(flattening,[],[f7])).
% 1.84/1.02  
% 1.84/1.02  fof(f17,plain,(
% 1.84/1.02    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.84/1.02    inference(nnf_transformation,[],[f8])).
% 1.84/1.02  
% 1.84/1.02  fof(f18,plain,(
% 1.84/1.02    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.84/1.02    inference(rectify,[],[f17])).
% 1.84/1.02  
% 1.84/1.02  fof(f19,plain,(
% 1.84/1.02    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK0(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.84/1.02    introduced(choice_axiom,[])).
% 1.84/1.02  
% 1.84/1.02  fof(f20,plain,(
% 1.84/1.02    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK0(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.84/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 1.84/1.02  
% 1.84/1.02  fof(f40,plain,(
% 1.84/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f20])).
% 1.84/1.02  
% 1.84/1.02  fof(f50,plain,(
% 1.84/1.02    l1_pre_topc(sK2)),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f49,plain,(
% 1.84/1.02    v2_pre_topc(sK2)),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f59,plain,(
% 1.84/1.02    v3_pre_topc(sK5,sK2)),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f1,axiom,(
% 1.84/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f15,plain,(
% 1.84/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/1.02    inference(nnf_transformation,[],[f1])).
% 1.84/1.02  
% 1.84/1.02  fof(f16,plain,(
% 1.84/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/1.02    inference(flattening,[],[f15])).
% 1.84/1.02  
% 1.84/1.02  fof(f33,plain,(
% 1.84/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.84/1.02    inference(cnf_transformation,[],[f16])).
% 1.84/1.02  
% 1.84/1.02  fof(f66,plain,(
% 1.84/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.84/1.02    inference(equality_resolution,[],[f33])).
% 1.84/1.02  
% 1.84/1.02  fof(f3,axiom,(
% 1.84/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f9,plain,(
% 1.84/1.02    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.84/1.02    inference(ennf_transformation,[],[f3])).
% 1.84/1.02  
% 1.84/1.02  fof(f10,plain,(
% 1.84/1.02    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.84/1.02    inference(flattening,[],[f9])).
% 1.84/1.02  
% 1.84/1.02  fof(f21,plain,(
% 1.84/1.02    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.84/1.02    inference(nnf_transformation,[],[f10])).
% 1.84/1.02  
% 1.84/1.02  fof(f42,plain,(
% 1.84/1.02    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f21])).
% 1.84/1.02  
% 1.84/1.02  fof(f52,plain,(
% 1.84/1.02    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f4,axiom,(
% 1.84/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f11,plain,(
% 1.84/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.84/1.02    inference(ennf_transformation,[],[f4])).
% 1.84/1.02  
% 1.84/1.02  fof(f12,plain,(
% 1.84/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.84/1.02    inference(flattening,[],[f11])).
% 1.84/1.02  
% 1.84/1.02  fof(f22,plain,(
% 1.84/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.84/1.02    inference(nnf_transformation,[],[f12])).
% 1.84/1.02  
% 1.84/1.02  fof(f43,plain,(
% 1.84/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f22])).
% 1.84/1.02  
% 1.84/1.02  fof(f68,plain,(
% 1.84/1.02    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.84/1.02    inference(equality_resolution,[],[f43])).
% 1.84/1.02  
% 1.84/1.02  fof(f55,plain,(
% 1.84/1.02    m1_pre_topc(sK4,sK2)),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f48,plain,(
% 1.84/1.02    ~v2_struct_0(sK2)),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f54,plain,(
% 1.84/1.02    ~v2_struct_0(sK4)),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f51,plain,(
% 1.84/1.02    v1_funct_1(sK3)),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f45,plain,(
% 1.84/1.02    ~v2_struct_0(sK1)),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f46,plain,(
% 1.84/1.02    v2_pre_topc(sK1)),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f47,plain,(
% 1.84/1.02    l1_pre_topc(sK1)),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f53,plain,(
% 1.84/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f61,plain,(
% 1.84/1.02    r1_tarski(sK5,u1_struct_0(sK4))),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f64,plain,(
% 1.84/1.02    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7) | ~r1_tmap_1(sK2,sK1,sK3,sK6)),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f62,plain,(
% 1.84/1.02    sK6 = sK7),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f58,plain,(
% 1.84/1.02    m1_subset_1(sK7,u1_struct_0(sK4))),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f57,plain,(
% 1.84/1.02    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f63,plain,(
% 1.84/1.02    r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7) | r1_tmap_1(sK2,sK1,sK3,sK6)),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  fof(f44,plain,(
% 1.84/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f22])).
% 1.84/1.02  
% 1.84/1.02  fof(f67,plain,(
% 1.84/1.02    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.84/1.02    inference(equality_resolution,[],[f44])).
% 1.84/1.02  
% 1.84/1.02  fof(f60,plain,(
% 1.84/1.02    r2_hidden(sK6,sK5)),
% 1.84/1.02    inference(cnf_transformation,[],[f32])).
% 1.84/1.02  
% 1.84/1.02  cnf(c_20,negated_conjecture,
% 1.84/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.84/1.02      inference(cnf_transformation,[],[f56]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_3155,plain,
% 1.84/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_3,plain,
% 1.84/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/1.02      | ~ v3_pre_topc(X0,X1)
% 1.84/1.02      | ~ r2_hidden(X3,X0)
% 1.84/1.02      | r2_hidden(X3,k1_tops_1(X1,X2))
% 1.84/1.02      | ~ r1_tarski(X0,X2)
% 1.84/1.02      | ~ v2_pre_topc(X1)
% 1.84/1.02      | ~ l1_pre_topc(X1) ),
% 1.84/1.02      inference(cnf_transformation,[],[f40]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_26,negated_conjecture,
% 1.84/1.02      ( l1_pre_topc(sK2) ),
% 1.84/1.02      inference(cnf_transformation,[],[f50]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1101,plain,
% 1.84/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/1.02      | ~ v3_pre_topc(X0,X1)
% 1.84/1.02      | ~ r2_hidden(X3,X0)
% 1.84/1.02      | r2_hidden(X3,k1_tops_1(X1,X2))
% 1.84/1.02      | ~ r1_tarski(X0,X2)
% 1.84/1.02      | ~ v2_pre_topc(X1)
% 1.84/1.02      | sK2 != X1 ),
% 1.84/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_26]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1102,plain,
% 1.84/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ v3_pre_topc(X1,sK2)
% 1.84/1.02      | ~ r2_hidden(X2,X1)
% 1.84/1.02      | r2_hidden(X2,k1_tops_1(sK2,X0))
% 1.84/1.02      | ~ r1_tarski(X1,X0)
% 1.84/1.02      | ~ v2_pre_topc(sK2) ),
% 1.84/1.02      inference(unflattening,[status(thm)],[c_1101]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_27,negated_conjecture,
% 1.84/1.02      ( v2_pre_topc(sK2) ),
% 1.84/1.02      inference(cnf_transformation,[],[f49]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1106,plain,
% 1.84/1.02      ( ~ r1_tarski(X1,X0)
% 1.84/1.02      | r2_hidden(X2,k1_tops_1(sK2,X0))
% 1.84/1.02      | ~ r2_hidden(X2,X1)
% 1.84/1.02      | ~ v3_pre_topc(X1,sK2)
% 1.84/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_1102,c_27]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1107,plain,
% 1.84/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ v3_pre_topc(X1,sK2)
% 1.84/1.02      | ~ r2_hidden(X2,X1)
% 1.84/1.02      | r2_hidden(X2,k1_tops_1(sK2,X0))
% 1.84/1.02      | ~ r1_tarski(X1,X0) ),
% 1.84/1.02      inference(renaming,[status(thm)],[c_1106]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_3145,plain,
% 1.84/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.84/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.84/1.02      | v3_pre_topc(X1,sK2) != iProver_top
% 1.84/1.02      | r2_hidden(X2,X1) != iProver_top
% 1.84/1.02      | r2_hidden(X2,k1_tops_1(sK2,X0)) = iProver_top
% 1.84/1.02      | r1_tarski(X1,X0) != iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_1107]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_4915,plain,
% 1.84/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.84/1.02      | v3_pre_topc(X0,sK2) != iProver_top
% 1.84/1.02      | r2_hidden(X1,X0) != iProver_top
% 1.84/1.02      | r2_hidden(X1,k1_tops_1(sK2,sK5)) = iProver_top
% 1.84/1.02      | r1_tarski(X0,sK5) != iProver_top ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_3155,c_3145]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_5029,plain,
% 1.84/1.02      ( v3_pre_topc(sK5,sK2) != iProver_top
% 1.84/1.02      | r2_hidden(X0,k1_tops_1(sK2,sK5)) = iProver_top
% 1.84/1.02      | r2_hidden(X0,sK5) != iProver_top
% 1.84/1.02      | r1_tarski(sK5,sK5) != iProver_top ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_3155,c_4915]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_17,negated_conjecture,
% 1.84/1.02      ( v3_pre_topc(sK5,sK2) ),
% 1.84/1.02      inference(cnf_transformation,[],[f59]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_46,plain,
% 1.84/1.02      ( v3_pre_topc(sK5,sK2) = iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_2,plain,
% 1.84/1.02      ( r1_tarski(X0,X0) ),
% 1.84/1.02      inference(cnf_transformation,[],[f66]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_3768,plain,
% 1.84/1.02      ( r1_tarski(sK5,sK5) ),
% 1.84/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_3771,plain,
% 1.84/1.02      ( r1_tarski(sK5,sK5) = iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_3768]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_5058,plain,
% 1.84/1.02      ( r2_hidden(X0,sK5) != iProver_top
% 1.84/1.02      | r2_hidden(X0,k1_tops_1(sK2,sK5)) = iProver_top ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_5029,c_46,c_3771]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_5059,plain,
% 1.84/1.02      ( r2_hidden(X0,k1_tops_1(sK2,sK5)) = iProver_top
% 1.84/1.02      | r2_hidden(X0,sK5) != iProver_top ),
% 1.84/1.02      inference(renaming,[status(thm)],[c_5058]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_8,plain,
% 1.84/1.02      ( m1_connsp_2(X0,X1,X2)
% 1.84/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.84/1.02      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.84/1.02      | v2_struct_0(X1)
% 1.84/1.02      | ~ v2_pre_topc(X1)
% 1.84/1.02      | ~ l1_pre_topc(X1) ),
% 1.84/1.02      inference(cnf_transformation,[],[f42]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_24,negated_conjecture,
% 1.84/1.02      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 1.84/1.02      inference(cnf_transformation,[],[f52]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_11,plain,
% 1.84/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.84/1.02      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.84/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.84/1.02      | ~ m1_connsp_2(X5,X0,X3)
% 1.84/1.02      | ~ m1_pre_topc(X4,X0)
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.84/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.84/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.84/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.84/1.02      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.84/1.02      | ~ v1_funct_1(X2)
% 1.84/1.02      | v2_struct_0(X1)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | v2_struct_0(X4)
% 1.84/1.02      | ~ v2_pre_topc(X1)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(X1)
% 1.84/1.02      | ~ l1_pre_topc(X0) ),
% 1.84/1.02      inference(cnf_transformation,[],[f68]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_21,negated_conjecture,
% 1.84/1.02      ( m1_pre_topc(sK4,sK2) ),
% 1.84/1.02      inference(cnf_transformation,[],[f55]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_452,plain,
% 1.84/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.84/1.02      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.84/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.84/1.02      | ~ m1_connsp_2(X5,X0,X3)
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.84/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.84/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.84/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.84/1.02      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.84/1.02      | ~ v1_funct_1(X2)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | v2_struct_0(X1)
% 1.84/1.02      | v2_struct_0(X4)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ v2_pre_topc(X1)
% 1.84/1.02      | ~ l1_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(X1)
% 1.84/1.02      | sK2 != X0
% 1.84/1.02      | sK4 != X4 ),
% 1.84/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_453,plain,
% 1.84/1.02      ( ~ r1_tmap_1(sK2,X0,X1,X2)
% 1.84/1.02      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
% 1.84/1.02      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 1.84/1.02      | ~ m1_connsp_2(X3,sK2,X2)
% 1.84/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.84/1.02      | ~ r1_tarski(X3,u1_struct_0(sK4))
% 1.84/1.02      | ~ v1_funct_1(X1)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | v2_struct_0(sK2)
% 1.84/1.02      | v2_struct_0(sK4)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ v2_pre_topc(sK2)
% 1.84/1.02      | ~ l1_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(sK2) ),
% 1.84/1.02      inference(unflattening,[status(thm)],[c_452]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_28,negated_conjecture,
% 1.84/1.02      ( ~ v2_struct_0(sK2) ),
% 1.84/1.02      inference(cnf_transformation,[],[f48]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_22,negated_conjecture,
% 1.84/1.02      ( ~ v2_struct_0(sK4) ),
% 1.84/1.02      inference(cnf_transformation,[],[f54]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_457,plain,
% 1.84/1.02      ( ~ l1_pre_topc(X0)
% 1.84/1.02      | ~ r1_tmap_1(sK2,X0,X1,X2)
% 1.84/1.02      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
% 1.84/1.02      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 1.84/1.02      | ~ m1_connsp_2(X3,sK2,X2)
% 1.84/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.84/1.02      | ~ r1_tarski(X3,u1_struct_0(sK4))
% 1.84/1.02      | ~ v1_funct_1(X1)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | ~ v2_pre_topc(X0) ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_453,c_28,c_27,c_26,c_22]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_458,plain,
% 1.84/1.02      ( ~ r1_tmap_1(sK2,X0,X1,X2)
% 1.84/1.02      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
% 1.84/1.02      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 1.84/1.02      | ~ m1_connsp_2(X3,sK2,X2)
% 1.84/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.84/1.02      | ~ r1_tarski(X3,u1_struct_0(sK4))
% 1.84/1.02      | ~ v1_funct_1(X1)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(X0) ),
% 1.84/1.02      inference(renaming,[status(thm)],[c_457]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_604,plain,
% 1.84/1.02      ( ~ r1_tmap_1(sK2,X0,X1,X2)
% 1.84/1.02      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
% 1.84/1.02      | ~ m1_connsp_2(X3,sK2,X2)
% 1.84/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.84/1.02      | ~ r1_tarski(X3,u1_struct_0(sK4))
% 1.84/1.02      | ~ v1_funct_1(X1)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(X0)
% 1.84/1.02      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.84/1.02      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.84/1.02      | sK3 != X1 ),
% 1.84/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_458]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_605,plain,
% 1.84/1.02      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 1.84/1.02      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.84/1.02      | ~ m1_connsp_2(X2,sK2,X1)
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.84/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.84/1.02      | ~ v1_funct_1(sK3)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(X0)
% 1.84/1.02      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 1.84/1.02      inference(unflattening,[status(thm)],[c_604]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_25,negated_conjecture,
% 1.84/1.02      ( v1_funct_1(sK3) ),
% 1.84/1.02      inference(cnf_transformation,[],[f51]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_609,plain,
% 1.84/1.02      ( ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.84/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_connsp_2(X2,sK2,X1)
% 1.84/1.02      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.84/1.02      | ~ r1_tmap_1(sK2,X0,sK3,X1)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(X0)
% 1.84/1.02      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_605,c_25]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_610,plain,
% 1.84/1.02      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 1.84/1.02      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.84/1.02      | ~ m1_connsp_2(X2,sK2,X1)
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.84/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(X0)
% 1.84/1.02      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 1.84/1.02      inference(renaming,[status(thm)],[c_609]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_655,plain,
% 1.84/1.02      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 1.84/1.02      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.84/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.84/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ r2_hidden(X5,k1_tops_1(X3,X2))
% 1.84/1.02      | ~ r1_tarski(X4,u1_struct_0(sK4))
% 1.84/1.02      | v2_struct_0(X3)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | ~ v2_pre_topc(X3)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(X3)
% 1.84/1.02      | ~ l1_pre_topc(X0)
% 1.84/1.02      | X4 != X2
% 1.84/1.02      | X1 != X5
% 1.84/1.02      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.84/1.02      | sK2 != X3 ),
% 1.84/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_610]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_656,plain,
% 1.84/1.02      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 1.84/1.02      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.84/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
% 1.84/1.02      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | v2_struct_0(sK2)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ v2_pre_topc(sK2)
% 1.84/1.02      | ~ l1_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(sK2)
% 1.84/1.02      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 1.84/1.02      inference(unflattening,[status(thm)],[c_655]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_660,plain,
% 1.84/1.02      ( ~ l1_pre_topc(X0)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.84/1.02      | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
% 1.84/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.84/1.02      | ~ r1_tmap_1(sK2,X0,sK3,X1)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_656,c_28,c_27,c_26]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_661,plain,
% 1.84/1.02      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 1.84/1.02      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.84/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
% 1.84/1.02      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(X0)
% 1.84/1.02      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 1.84/1.02      inference(renaming,[status(thm)],[c_660]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_31,negated_conjecture,
% 1.84/1.02      ( ~ v2_struct_0(sK1) ),
% 1.84/1.02      inference(cnf_transformation,[],[f45]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_941,plain,
% 1.84/1.02      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 1.84/1.02      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.84/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
% 1.84/1.02      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(X0)
% 1.84/1.02      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.84/1.02      | sK1 != X0 ),
% 1.84/1.02      inference(resolution_lifted,[status(thm)],[c_661,c_31]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_942,plain,
% 1.84/1.02      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 1.84/1.02      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.84/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.84/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.84/1.02      | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
% 1.84/1.02      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 1.84/1.02      | ~ v2_pre_topc(sK1)
% 1.84/1.02      | ~ l1_pre_topc(sK1)
% 1.84/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.84/1.02      inference(unflattening,[status(thm)],[c_941]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_30,negated_conjecture,
% 1.84/1.02      ( v2_pre_topc(sK1) ),
% 1.84/1.02      inference(cnf_transformation,[],[f46]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_29,negated_conjecture,
% 1.84/1.02      ( l1_pre_topc(sK1) ),
% 1.84/1.02      inference(cnf_transformation,[],[f47]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_23,negated_conjecture,
% 1.84/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 1.84/1.02      inference(cnf_transformation,[],[f53]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_946,plain,
% 1.84/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.84/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.84/1.02      | ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 1.84/1.02      | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
% 1.84/1.02      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 1.84/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_942,c_30,c_29,c_23]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_947,plain,
% 1.84/1.02      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 1.84/1.02      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.84/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.84/1.02      | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
% 1.84/1.02      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 1.84/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.84/1.02      inference(renaming,[status(thm)],[c_946]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1944,plain,
% 1.84/1.02      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 1.84/1.02      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.84/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.84/1.02      | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
% 1.84/1.02      | ~ r1_tarski(X1,u1_struct_0(sK4)) ),
% 1.84/1.02      inference(equality_resolution_simp,[status(thm)],[c_947]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_3131,plain,
% 1.84/1.02      ( r1_tmap_1(sK2,sK1,sK3,X0) != iProver_top
% 1.84/1.02      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0) = iProver_top
% 1.84/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.84/1.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 1.84/1.02      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 1.84/1.02      | r2_hidden(X0,k1_tops_1(sK2,X1)) != iProver_top
% 1.84/1.02      | r1_tarski(X1,u1_struct_0(sK4)) != iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_1944]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_4036,plain,
% 1.84/1.02      ( r1_tmap_1(sK2,sK1,sK3,X0) != iProver_top
% 1.84/1.02      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0) = iProver_top
% 1.84/1.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 1.84/1.02      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 1.84/1.02      | r2_hidden(X0,k1_tops_1(sK2,sK5)) != iProver_top
% 1.84/1.02      | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_3155,c_3131]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_15,negated_conjecture,
% 1.84/1.02      ( r1_tarski(sK5,u1_struct_0(sK4)) ),
% 1.84/1.02      inference(cnf_transformation,[],[f61]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_48,plain,
% 1.84/1.02      ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_4193,plain,
% 1.84/1.02      ( r2_hidden(X0,k1_tops_1(sK2,sK5)) != iProver_top
% 1.84/1.02      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 1.84/1.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 1.84/1.02      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0) = iProver_top
% 1.84/1.02      | r1_tmap_1(sK2,sK1,sK3,X0) != iProver_top ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_4036,c_48]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_4194,plain,
% 1.84/1.02      ( r1_tmap_1(sK2,sK1,sK3,X0) != iProver_top
% 1.84/1.02      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0) = iProver_top
% 1.84/1.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 1.84/1.02      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 1.84/1.02      | r2_hidden(X0,k1_tops_1(sK2,sK5)) != iProver_top ),
% 1.84/1.02      inference(renaming,[status(thm)],[c_4193]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_12,negated_conjecture,
% 1.84/1.02      ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
% 1.84/1.02      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7) ),
% 1.84/1.02      inference(cnf_transformation,[],[f64]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_3162,plain,
% 1.84/1.02      ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
% 1.84/1.02      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7) != iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_14,negated_conjecture,
% 1.84/1.02      ( sK6 = sK7 ),
% 1.84/1.02      inference(cnf_transformation,[],[f62]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_3196,plain,
% 1.84/1.02      ( r1_tmap_1(sK2,sK1,sK3,sK7) != iProver_top
% 1.84/1.02      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7) != iProver_top ),
% 1.84/1.02      inference(light_normalisation,[status(thm)],[c_3162,c_14]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_4204,plain,
% 1.84/1.02      ( r1_tmap_1(sK2,sK1,sK3,sK7) != iProver_top
% 1.84/1.02      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
% 1.84/1.02      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 1.84/1.02      | r2_hidden(sK7,k1_tops_1(sK2,sK5)) != iProver_top ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_4194,c_3196]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_18,negated_conjecture,
% 1.84/1.02      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 1.84/1.02      inference(cnf_transformation,[],[f58]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_45,plain,
% 1.84/1.02      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_19,negated_conjecture,
% 1.84/1.02      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 1.84/1.02      inference(cnf_transformation,[],[f57]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_3156,plain,
% 1.84/1.02      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_3174,plain,
% 1.84/1.02      ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
% 1.84/1.02      inference(light_normalisation,[status(thm)],[c_3156,c_14]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_13,negated_conjecture,
% 1.84/1.02      ( r1_tmap_1(sK2,sK1,sK3,sK6)
% 1.84/1.02      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7) ),
% 1.84/1.02      inference(cnf_transformation,[],[f63]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_3161,plain,
% 1.84/1.02      ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
% 1.84/1.02      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7) = iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_3191,plain,
% 1.84/1.02      ( r1_tmap_1(sK2,sK1,sK3,sK7) = iProver_top
% 1.84/1.02      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK7) = iProver_top ),
% 1.84/1.02      inference(light_normalisation,[status(thm)],[c_3161,c_14]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_10,plain,
% 1.84/1.02      ( r1_tmap_1(X0,X1,X2,X3)
% 1.84/1.02      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.84/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.84/1.02      | ~ m1_connsp_2(X5,X0,X3)
% 1.84/1.02      | ~ m1_pre_topc(X4,X0)
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.84/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.84/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.84/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.84/1.02      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.84/1.02      | ~ v1_funct_1(X2)
% 1.84/1.02      | v2_struct_0(X1)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | v2_struct_0(X4)
% 1.84/1.02      | ~ v2_pre_topc(X1)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(X1)
% 1.84/1.02      | ~ l1_pre_topc(X0) ),
% 1.84/1.02      inference(cnf_transformation,[],[f67]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_503,plain,
% 1.84/1.02      ( r1_tmap_1(X0,X1,X2,X3)
% 1.84/1.02      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.84/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.84/1.02      | ~ m1_connsp_2(X5,X0,X3)
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.84/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.84/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.84/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.84/1.02      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.84/1.02      | ~ v1_funct_1(X2)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | v2_struct_0(X1)
% 1.84/1.02      | v2_struct_0(X4)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ v2_pre_topc(X1)
% 1.84/1.02      | ~ l1_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(X1)
% 1.84/1.02      | sK2 != X0
% 1.84/1.02      | sK4 != X4 ),
% 1.84/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_504,plain,
% 1.84/1.02      ( r1_tmap_1(sK2,X0,X1,X2)
% 1.84/1.02      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
% 1.84/1.02      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 1.84/1.02      | ~ m1_connsp_2(X3,sK2,X2)
% 1.84/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.84/1.02      | ~ r1_tarski(X3,u1_struct_0(sK4))
% 1.84/1.02      | ~ v1_funct_1(X1)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | v2_struct_0(sK2)
% 1.84/1.02      | v2_struct_0(sK4)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ v2_pre_topc(sK2)
% 1.84/1.02      | ~ l1_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(sK2) ),
% 1.84/1.02      inference(unflattening,[status(thm)],[c_503]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_508,plain,
% 1.84/1.02      ( ~ l1_pre_topc(X0)
% 1.84/1.02      | r1_tmap_1(sK2,X0,X1,X2)
% 1.84/1.02      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
% 1.84/1.02      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 1.84/1.02      | ~ m1_connsp_2(X3,sK2,X2)
% 1.84/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.84/1.02      | ~ r1_tarski(X3,u1_struct_0(sK4))
% 1.84/1.02      | ~ v1_funct_1(X1)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | ~ v2_pre_topc(X0) ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_504,c_28,c_27,c_26,c_22]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_509,plain,
% 1.84/1.02      ( r1_tmap_1(sK2,X0,X1,X2)
% 1.84/1.02      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
% 1.84/1.02      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 1.84/1.02      | ~ m1_connsp_2(X3,sK2,X2)
% 1.84/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.84/1.02      | ~ r1_tarski(X3,u1_struct_0(sK4))
% 1.84/1.02      | ~ v1_funct_1(X1)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(X0) ),
% 1.84/1.02      inference(renaming,[status(thm)],[c_508]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_556,plain,
% 1.84/1.02      ( r1_tmap_1(sK2,X0,X1,X2)
% 1.84/1.02      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
% 1.84/1.02      | ~ m1_connsp_2(X3,sK2,X2)
% 1.84/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.84/1.02      | ~ r1_tarski(X3,u1_struct_0(sK4))
% 1.84/1.02      | ~ v1_funct_1(X1)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(X0)
% 1.84/1.02      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.84/1.02      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.84/1.02      | sK3 != X1 ),
% 1.84/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_509]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_557,plain,
% 1.84/1.02      ( r1_tmap_1(sK2,X0,sK3,X1)
% 1.84/1.02      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.84/1.02      | ~ m1_connsp_2(X2,sK2,X1)
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.84/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.84/1.02      | ~ v1_funct_1(sK3)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(X0)
% 1.84/1.02      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 1.84/1.02      inference(unflattening,[status(thm)],[c_556]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_561,plain,
% 1.84/1.02      ( ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.84/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_connsp_2(X2,sK2,X1)
% 1.84/1.02      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.84/1.02      | r1_tmap_1(sK2,X0,sK3,X1)
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(X0)
% 1.84/1.02      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_557,c_25]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_562,plain,
% 1.84/1.02      ( r1_tmap_1(sK2,X0,sK3,X1)
% 1.84/1.02      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.84/1.02      | ~ m1_connsp_2(X2,sK2,X1)
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.84/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.84/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.02      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.84/1.02      | v2_struct_0(X0)
% 1.84/1.02      | ~ v2_pre_topc(X0)
% 1.84/1.02      | ~ l1_pre_topc(X0)
% 1.84/1.02      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 1.84/1.03      inference(renaming,[status(thm)],[c_561]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_701,plain,
% 1.84/1.03      ( r1_tmap_1(sK2,X0,sK3,X1)
% 1.84/1.03      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.84/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.84/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.03      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 1.84/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.84/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.84/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.03      | ~ r2_hidden(X5,k1_tops_1(X3,X2))
% 1.84/1.03      | ~ r1_tarski(X4,u1_struct_0(sK4))
% 1.84/1.03      | v2_struct_0(X3)
% 1.84/1.03      | v2_struct_0(X0)
% 1.84/1.03      | ~ v2_pre_topc(X3)
% 1.84/1.03      | ~ v2_pre_topc(X0)
% 1.84/1.03      | ~ l1_pre_topc(X3)
% 1.84/1.03      | ~ l1_pre_topc(X0)
% 1.84/1.03      | X4 != X2
% 1.84/1.03      | X1 != X5
% 1.84/1.03      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.84/1.03      | sK2 != X3 ),
% 1.84/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_562]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_702,plain,
% 1.84/1.03      ( r1_tmap_1(sK2,X0,sK3,X1)
% 1.84/1.03      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.84/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.84/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.84/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.03      | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
% 1.84/1.03      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.84/1.03      | v2_struct_0(X0)
% 1.84/1.03      | v2_struct_0(sK2)
% 1.84/1.03      | ~ v2_pre_topc(X0)
% 1.84/1.03      | ~ v2_pre_topc(sK2)
% 1.84/1.03      | ~ l1_pre_topc(X0)
% 1.84/1.03      | ~ l1_pre_topc(sK2)
% 1.84/1.03      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 1.84/1.03      inference(unflattening,[status(thm)],[c_701]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_706,plain,
% 1.84/1.03      ( ~ l1_pre_topc(X0)
% 1.84/1.03      | v2_struct_0(X0)
% 1.84/1.03      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.84/1.03      | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
% 1.84/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.84/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.84/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.03      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.84/1.03      | r1_tmap_1(sK2,X0,sK3,X1)
% 1.84/1.03      | ~ v2_pre_topc(X0)
% 1.84/1.03      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 1.84/1.03      inference(global_propositional_subsumption,
% 1.84/1.03                [status(thm)],
% 1.84/1.03                [c_702,c_28,c_27,c_26]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_707,plain,
% 1.84/1.03      ( r1_tmap_1(sK2,X0,sK3,X1)
% 1.84/1.03      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.84/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.84/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.84/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.03      | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
% 1.84/1.03      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.84/1.03      | v2_struct_0(X0)
% 1.84/1.03      | ~ v2_pre_topc(X0)
% 1.84/1.03      | ~ l1_pre_topc(X0)
% 1.84/1.03      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 1.84/1.03      inference(renaming,[status(thm)],[c_706]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_905,plain,
% 1.84/1.03      ( r1_tmap_1(sK2,X0,sK3,X1)
% 1.84/1.03      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.84/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.84/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.84/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.84/1.03      | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
% 1.84/1.03      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.84/1.03      | ~ v2_pre_topc(X0)
% 1.84/1.03      | ~ l1_pre_topc(X0)
% 1.84/1.03      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.84/1.03      | sK1 != X0 ),
% 1.84/1.03      inference(resolution_lifted,[status(thm)],[c_707,c_31]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_906,plain,
% 1.84/1.03      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 1.84/1.03      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.84/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.84/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.84/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.84/1.03      | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
% 1.84/1.03      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 1.84/1.03      | ~ v2_pre_topc(sK1)
% 1.84/1.03      | ~ l1_pre_topc(sK1)
% 1.84/1.03      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.84/1.03      inference(unflattening,[status(thm)],[c_905]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_910,plain,
% 1.84/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.84/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.84/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.03      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.84/1.03      | r1_tmap_1(sK2,sK1,sK3,X0)
% 1.84/1.03      | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
% 1.84/1.03      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 1.84/1.03      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.84/1.03      inference(global_propositional_subsumption,
% 1.84/1.03                [status(thm)],
% 1.84/1.03                [c_906,c_30,c_29,c_23]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_911,plain,
% 1.84/1.03      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 1.84/1.03      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.84/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.84/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.84/1.03      | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
% 1.84/1.03      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 1.84/1.03      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.84/1.03      inference(renaming,[status(thm)],[c_910]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_1948,plain,
% 1.84/1.03      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 1.84/1.03      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.84/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.84/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.84/1.03      | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
% 1.84/1.03      | ~ r1_tarski(X1,u1_struct_0(sK4)) ),
% 1.84/1.03      inference(equality_resolution_simp,[status(thm)],[c_911]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_3130,plain,
% 1.84/1.03      ( r1_tmap_1(sK2,sK1,sK3,X0) = iProver_top
% 1.84/1.03      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0) != iProver_top
% 1.84/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.84/1.03      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 1.84/1.03      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 1.84/1.03      | r2_hidden(X0,k1_tops_1(sK2,X1)) != iProver_top
% 1.84/1.03      | r1_tarski(X1,u1_struct_0(sK4)) != iProver_top ),
% 1.84/1.03      inference(predicate_to_equality,[status(thm)],[c_1948]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_3713,plain,
% 1.84/1.03      ( r1_tmap_1(sK2,sK1,sK3,sK7) = iProver_top
% 1.84/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.84/1.03      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
% 1.84/1.03      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 1.84/1.03      | r2_hidden(sK7,k1_tops_1(sK2,X0)) != iProver_top
% 1.84/1.03      | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
% 1.84/1.03      inference(superposition,[status(thm)],[c_3191,c_3130]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_4118,plain,
% 1.84/1.03      ( r1_tmap_1(sK2,sK1,sK3,sK7) = iProver_top
% 1.84/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.84/1.03      | r2_hidden(sK7,k1_tops_1(sK2,X0)) != iProver_top
% 1.84/1.03      | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
% 1.84/1.03      inference(global_propositional_subsumption,
% 1.84/1.03                [status(thm)],
% 1.84/1.03                [c_3713,c_45,c_3174]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_4128,plain,
% 1.84/1.03      ( r1_tmap_1(sK2,sK1,sK3,sK7) = iProver_top
% 1.84/1.03      | r2_hidden(sK7,k1_tops_1(sK2,sK5)) != iProver_top
% 1.84/1.03      | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
% 1.84/1.03      inference(superposition,[status(thm)],[c_3155,c_4118]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_4131,plain,
% 1.84/1.03      ( r2_hidden(sK7,k1_tops_1(sK2,sK5)) != iProver_top
% 1.84/1.03      | r1_tmap_1(sK2,sK1,sK3,sK7) = iProver_top ),
% 1.84/1.03      inference(global_propositional_subsumption,
% 1.84/1.03                [status(thm)],
% 1.84/1.03                [c_4128,c_48]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_4132,plain,
% 1.84/1.03      ( r1_tmap_1(sK2,sK1,sK3,sK7) = iProver_top
% 1.84/1.03      | r2_hidden(sK7,k1_tops_1(sK2,sK5)) != iProver_top ),
% 1.84/1.03      inference(renaming,[status(thm)],[c_4131]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_4711,plain,
% 1.84/1.03      ( r2_hidden(sK7,k1_tops_1(sK2,sK5)) != iProver_top ),
% 1.84/1.03      inference(global_propositional_subsumption,
% 1.84/1.03                [status(thm)],
% 1.84/1.03                [c_4204,c_45,c_3174,c_4132]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_5066,plain,
% 1.84/1.03      ( r2_hidden(sK7,sK5) != iProver_top ),
% 1.84/1.03      inference(superposition,[status(thm)],[c_5059,c_4711]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_16,negated_conjecture,
% 1.84/1.03      ( r2_hidden(sK6,sK5) ),
% 1.84/1.03      inference(cnf_transformation,[],[f60]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_3159,plain,
% 1.84/1.03      ( r2_hidden(sK6,sK5) = iProver_top ),
% 1.84/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(c_3169,plain,
% 1.84/1.03      ( r2_hidden(sK7,sK5) = iProver_top ),
% 1.84/1.03      inference(light_normalisation,[status(thm)],[c_3159,c_14]) ).
% 1.84/1.03  
% 1.84/1.03  cnf(contradiction,plain,
% 1.84/1.03      ( $false ),
% 1.84/1.03      inference(minisat,[status(thm)],[c_5066,c_3169]) ).
% 1.84/1.03  
% 1.84/1.03  
% 1.84/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.84/1.03  
% 1.84/1.03  ------                               Statistics
% 1.84/1.03  
% 1.84/1.03  ------ General
% 1.84/1.03  
% 1.84/1.03  abstr_ref_over_cycles:                  0
% 1.84/1.03  abstr_ref_under_cycles:                 0
% 1.84/1.03  gc_basic_clause_elim:                   0
% 1.84/1.03  forced_gc_time:                         0
% 1.84/1.03  parsing_time:                           0.013
% 1.84/1.03  unif_index_cands_time:                  0.
% 1.84/1.03  unif_index_add_time:                    0.
% 1.84/1.03  orderings_time:                         0.
% 1.84/1.03  out_proof_time:                         0.019
% 1.84/1.03  total_time:                             0.231
% 1.84/1.03  num_of_symbols:                         60
% 1.84/1.03  num_of_terms:                           2651
% 1.84/1.03  
% 1.84/1.03  ------ Preprocessing
% 1.84/1.03  
% 1.84/1.03  num_of_splits:                          6
% 1.84/1.03  num_of_split_atoms:                     4
% 1.84/1.03  num_of_reused_defs:                     2
% 1.84/1.03  num_eq_ax_congr_red:                    14
% 1.84/1.03  num_of_sem_filtered_clauses:            1
% 1.84/1.03  num_of_subtypes:                        0
% 1.84/1.03  monotx_restored_types:                  0
% 1.84/1.03  sat_num_of_epr_types:                   0
% 1.84/1.03  sat_num_of_non_cyclic_types:            0
% 1.84/1.03  sat_guarded_non_collapsed_types:        0
% 1.84/1.03  num_pure_diseq_elim:                    0
% 1.84/1.03  simp_replaced_by:                       0
% 1.84/1.03  res_preprocessed:                       156
% 1.84/1.03  prep_upred:                             0
% 1.84/1.03  prep_unflattend:                        44
% 1.84/1.03  smt_new_axioms:                         0
% 1.84/1.03  pred_elim_cands:                        5
% 1.84/1.03  pred_elim:                              7
% 1.84/1.03  pred_elim_cl:                           1
% 1.84/1.03  pred_elim_cycles:                       11
% 1.84/1.03  merged_defs:                            8
% 1.84/1.03  merged_defs_ncl:                        0
% 1.84/1.03  bin_hyper_res:                          8
% 1.84/1.03  prep_cycles:                            4
% 1.84/1.03  pred_elim_time:                         0.058
% 1.84/1.03  splitting_time:                         0.
% 1.84/1.03  sem_filter_time:                        0.
% 1.84/1.03  monotx_time:                            0.001
% 1.84/1.03  subtype_inf_time:                       0.
% 1.84/1.03  
% 1.84/1.03  ------ Problem properties
% 1.84/1.03  
% 1.84/1.03  clauses:                                36
% 1.84/1.03  conjectures:                            10
% 1.84/1.03  epr:                                    5
% 1.84/1.03  horn:                                   35
% 1.84/1.03  ground:                                 16
% 1.84/1.03  unary:                                  9
% 1.84/1.03  binary:                                 2
% 1.84/1.03  lits:                                   136
% 1.84/1.03  lits_eq:                                12
% 1.84/1.03  fd_pure:                                0
% 1.84/1.03  fd_pseudo:                              0
% 1.84/1.03  fd_cond:                                0
% 1.84/1.03  fd_pseudo_cond:                         1
% 1.84/1.03  ac_symbols:                             0
% 1.84/1.03  
% 1.84/1.03  ------ Propositional Solver
% 1.84/1.03  
% 1.84/1.03  prop_solver_calls:                      26
% 1.84/1.03  prop_fast_solver_calls:                 1854
% 1.84/1.03  smt_solver_calls:                       0
% 1.84/1.03  smt_fast_solver_calls:                  0
% 1.84/1.03  prop_num_of_clauses:                    1109
% 1.84/1.03  prop_preprocess_simplified:             4981
% 1.84/1.03  prop_fo_subsumed:                       51
% 1.84/1.03  prop_solver_time:                       0.
% 1.84/1.03  smt_solver_time:                        0.
% 1.84/1.03  smt_fast_solver_time:                   0.
% 1.84/1.03  prop_fast_solver_time:                  0.
% 1.84/1.03  prop_unsat_core_time:                   0.
% 1.84/1.03  
% 1.84/1.03  ------ QBF
% 1.84/1.03  
% 1.84/1.03  qbf_q_res:                              0
% 1.84/1.03  qbf_num_tautologies:                    0
% 1.84/1.03  qbf_prep_cycles:                        0
% 1.84/1.03  
% 1.84/1.03  ------ BMC1
% 1.84/1.03  
% 1.84/1.03  bmc1_current_bound:                     -1
% 1.84/1.03  bmc1_last_solved_bound:                 -1
% 1.84/1.03  bmc1_unsat_core_size:                   -1
% 1.84/1.03  bmc1_unsat_core_parents_size:           -1
% 1.84/1.03  bmc1_merge_next_fun:                    0
% 1.84/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.84/1.03  
% 1.84/1.03  ------ Instantiation
% 1.84/1.03  
% 1.84/1.03  inst_num_of_clauses:                    289
% 1.84/1.03  inst_num_in_passive:                    87
% 1.84/1.03  inst_num_in_active:                     199
% 1.84/1.03  inst_num_in_unprocessed:                4
% 1.84/1.03  inst_num_of_loops:                      210
% 1.84/1.03  inst_num_of_learning_restarts:          0
% 1.84/1.03  inst_num_moves_active_passive:          8
% 1.84/1.03  inst_lit_activity:                      0
% 1.84/1.03  inst_lit_activity_moves:                0
% 1.84/1.03  inst_num_tautologies:                   0
% 1.84/1.03  inst_num_prop_implied:                  0
% 1.84/1.03  inst_num_existing_simplified:           0
% 1.84/1.03  inst_num_eq_res_simplified:             0
% 1.84/1.03  inst_num_child_elim:                    0
% 1.84/1.03  inst_num_of_dismatching_blockings:      31
% 1.84/1.03  inst_num_of_non_proper_insts:           321
% 1.84/1.03  inst_num_of_duplicates:                 0
% 1.84/1.03  inst_inst_num_from_inst_to_res:         0
% 1.84/1.03  inst_dismatching_checking_time:         0.
% 1.84/1.03  
% 1.84/1.03  ------ Resolution
% 1.84/1.03  
% 1.84/1.03  res_num_of_clauses:                     0
% 1.84/1.03  res_num_in_passive:                     0
% 1.84/1.03  res_num_in_active:                      0
% 1.84/1.03  res_num_of_loops:                       160
% 1.84/1.03  res_forward_subset_subsumed:            54
% 1.84/1.03  res_backward_subset_subsumed:           4
% 1.84/1.03  res_forward_subsumed:                   0
% 1.84/1.03  res_backward_subsumed:                  0
% 1.84/1.03  res_forward_subsumption_resolution:     5
% 1.84/1.03  res_backward_subsumption_resolution:    0
% 1.84/1.03  res_clause_to_clause_subsumption:       198
% 1.84/1.03  res_orphan_elimination:                 0
% 1.84/1.03  res_tautology_del:                      45
% 1.84/1.03  res_num_eq_res_simplified:              2
% 1.84/1.03  res_num_sel_changes:                    0
% 1.84/1.03  res_moves_from_active_to_pass:          0
% 1.84/1.03  
% 1.84/1.03  ------ Superposition
% 1.84/1.03  
% 1.84/1.03  sup_time_total:                         0.
% 1.84/1.03  sup_time_generating:                    0.
% 1.84/1.03  sup_time_sim_full:                      0.
% 1.84/1.03  sup_time_sim_immed:                     0.
% 1.84/1.03  
% 1.84/1.03  sup_num_of_clauses:                     53
% 1.84/1.03  sup_num_in_active:                      42
% 1.84/1.03  sup_num_in_passive:                     11
% 1.84/1.03  sup_num_of_loops:                       41
% 1.84/1.03  sup_fw_superposition:                   13
% 1.84/1.03  sup_bw_superposition:                   9
% 1.84/1.03  sup_immediate_simplified:               0
% 1.84/1.03  sup_given_eliminated:                   0
% 1.84/1.03  comparisons_done:                       0
% 1.84/1.03  comparisons_avoided:                    0
% 1.84/1.03  
% 1.84/1.03  ------ Simplifications
% 1.84/1.03  
% 1.84/1.03  
% 1.84/1.03  sim_fw_subset_subsumed:                 0
% 1.84/1.03  sim_bw_subset_subsumed:                 0
% 1.84/1.03  sim_fw_subsumed:                        0
% 1.84/1.03  sim_bw_subsumed:                        1
% 1.84/1.03  sim_fw_subsumption_res:                 0
% 1.84/1.03  sim_bw_subsumption_res:                 0
% 1.84/1.03  sim_tautology_del:                      2
% 1.84/1.03  sim_eq_tautology_del:                   1
% 1.84/1.03  sim_eq_res_simp:                        0
% 1.84/1.03  sim_fw_demodulated:                     0
% 1.84/1.03  sim_bw_demodulated:                     0
% 1.84/1.03  sim_light_normalised:                   4
% 1.84/1.03  sim_joinable_taut:                      0
% 1.84/1.03  sim_joinable_simp:                      0
% 1.84/1.03  sim_ac_normalised:                      0
% 1.84/1.03  sim_smt_subsumption:                    0
% 1.84/1.03  
%------------------------------------------------------------------------------
