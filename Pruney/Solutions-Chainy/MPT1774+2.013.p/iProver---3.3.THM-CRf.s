%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:14 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 586 expanded)
%              Number of clauses        :   99 ( 114 expanded)
%              Number of leaves         :   23 ( 258 expanded)
%              Depth                    :   22
%              Number of atoms          : 1542 (12347 expanded)
%              Number of equality atoms :  149 ( 735 expanded)
%              Maximal formula depth    :   31 (   9 average)
%              Maximal clause size      :   50 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f28,f36,f35,f34,f33,f32,f31,f30,f29])).

fof(f66,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

fof(f46,plain,(
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

fof(f73,plain,(
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
    inference(equality_resolution,[],[f46])).

fof(f59,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
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

fof(f72,plain,(
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
    inference(equality_resolution,[],[f47])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f71,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f68,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f52,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1486,plain,
    ( ~ r1_tmap_1(X0_52,X1_52,X0_53,X1_53)
    | r1_tmap_1(X0_52,X1_52,X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_2782,plain,
    ( r1_tmap_1(sK2,sK0,X0_53,X1_53)
    | ~ r1_tmap_1(sK2,sK0,X2_53,sK6)
    | X0_53 != X2_53
    | X1_53 != sK6 ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_3119,plain,
    ( ~ r1_tmap_1(sK2,sK0,X0_53,sK6)
    | r1_tmap_1(sK2,sK0,X1_53,sK7)
    | X1_53 != X0_53
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_2782])).

cnf(c_3607,plain,
    ( r1_tmap_1(sK2,sK0,X0_53,sK7)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X1_53),sK6)
    | X0_53 != k3_tmap_1(sK1,sK0,sK3,sK2,X1_53)
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_3119])).

cnf(c_4469,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_3607])).

cnf(c_6,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,X0)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_400,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK5 != X0
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_401,plain,
    ( m1_connsp_2(sK5,X0,sK6)
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f73])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_435,plain,
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
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_436,plain,
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
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_440,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_22])).

cnf(c_441,plain,
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
    inference(renaming,[status(thm)],[c_440])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_488,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_441,c_7])).

cnf(c_658,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ v3_pre_topc(sK5,X5)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(X6,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X5)))
    | ~ m1_subset_1(sK6,u1_struct_0(X5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X5)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | X3 != X5
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK5 != X6
    | sK6 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_401,c_488])).

cnf(c_659,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | ~ r1_tmap_1(X3,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_658])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_707,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | ~ r1_tmap_1(X3,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
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
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_659,c_2,c_3])).

cnf(c_1448,plain,
    ( r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,X3_52,X0_52,sK4),sK6)
    | ~ r1_tmap_1(X3_52,X1_52,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | ~ m1_pre_topc(X3_52,X2_52)
    | ~ r1_tarski(sK5,u1_struct_0(X0_52))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_52)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_52))
    | ~ m1_subset_1(sK6,u1_struct_0(X3_52))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(X3_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | u1_struct_0(X3_52) != u1_struct_0(sK3)
    | u1_struct_0(X1_52) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_707])).

cnf(c_3004,plain,
    ( r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,sK3,X0_52,sK4),sK6)
    | ~ r1_tmap_1(sK3,X1_52,sK4,sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(X0_52,sK3)
    | ~ m1_pre_topc(sK3,X2_52)
    | ~ r1_tarski(sK5,u1_struct_0(X0_52))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_52))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_52))))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | u1_struct_0(X1_52) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1448])).

cnf(c_3382,plain,
    ( ~ r1_tmap_1(sK3,X0_52,sK4,sK6)
    | r1_tmap_1(sK2,X0_52,k3_tmap_1(X1_52,X0_52,sK3,sK2,sK4),sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK3,X1_52)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52))))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X0_52)
    | u1_struct_0(X0_52) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3004])).

cnf(c_3986,plain,
    ( ~ r1_tmap_1(sK3,X0_52,sK4,sK6)
    | r1_tmap_1(sK2,X0_52,k3_tmap_1(sK1,X0_52,sK3,sK2,sK4),sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52))))
    | v2_struct_0(X0_52)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_52) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3382])).

cnf(c_3988,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3986])).

cnf(c_1479,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_3924,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1479])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f72])).

cnf(c_510,plain,
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
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_511,plain,
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
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_515,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_511,c_22])).

cnf(c_516,plain,
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
    inference(renaming,[status(thm)],[c_515])).

cnf(c_563,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_516,c_7])).

cnf(c_587,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v3_pre_topc(sK5,X5)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(X6,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X5)))
    | ~ m1_subset_1(sK6,u1_struct_0(X5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X5)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | X3 != X5
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK5 != X6
    | sK6 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_401,c_563])).

cnf(c_588,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | r1_tmap_1(X3,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_636,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | r1_tmap_1(X3,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
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
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_588,c_2,c_3])).

cnf(c_1449,plain,
    ( ~ r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,X3_52,X0_52,sK4),sK6)
    | r1_tmap_1(X3_52,X1_52,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | ~ m1_pre_topc(X3_52,X2_52)
    | ~ r1_tarski(sK5,u1_struct_0(X0_52))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_52)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_52))
    | ~ m1_subset_1(sK6,u1_struct_0(X3_52))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(X3_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | u1_struct_0(X3_52) != u1_struct_0(sK3)
    | u1_struct_0(X1_52) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_636])).

cnf(c_3003,plain,
    ( ~ r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,sK3,X0_52,sK4),sK6)
    | r1_tmap_1(sK3,X1_52,sK4,sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(X0_52,sK3)
    | ~ m1_pre_topc(sK3,X2_52)
    | ~ r1_tarski(sK5,u1_struct_0(X0_52))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_52))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_52))))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | u1_struct_0(X1_52) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1449])).

cnf(c_3377,plain,
    ( r1_tmap_1(sK3,X0_52,sK4,sK6)
    | ~ r1_tmap_1(sK2,X0_52,k3_tmap_1(X1_52,X0_52,sK3,sK2,sK4),sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK3,X1_52)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52))))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X0_52)
    | u1_struct_0(X0_52) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3003])).

cnf(c_3557,plain,
    ( r1_tmap_1(sK3,X0_52,sK4,sK6)
    | ~ r1_tmap_1(sK2,X0_52,k3_tmap_1(sK1,X0_52,sK3,sK2,sK4),sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52))))
    | v2_struct_0(X0_52)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_52) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3377])).

cnf(c_3559,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3557])).

cnf(c_2516,plain,
    ( r1_tmap_1(sK2,sK0,X0_53,X1_53)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | X0_53 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | X1_53 != sK7 ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_2678,plain,
    ( r1_tmap_1(sK2,sK0,X0_53,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | X0_53 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2516])).

cnf(c_3359,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2678])).

cnf(c_2919,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1479])).

cnf(c_1487,plain,
    ( X0_53 != X1_53
    | k3_tmap_1(X0_52,X1_52,X2_52,X3_52,X0_53) = k3_tmap_1(X0_52,X1_52,X2_52,X3_52,X1_53) ),
    theory(equality)).

cnf(c_2846,plain,
    ( X0_53 != sK4
    | k3_tmap_1(sK1,sK0,sK3,sK2,X0_53) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1487])).

cnf(c_2849,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2846])).

cnf(c_1473,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ l1_pre_topc(X1_52)
    | l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2710,plain,
    ( ~ m1_pre_topc(sK3,X0_52)
    | ~ l1_pre_topc(X0_52)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1473])).

cnf(c_2839,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2710])).

cnf(c_1480,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_2627,plain,
    ( X0_53 != X1_53
    | X0_53 = sK6
    | sK6 != X1_53 ),
    inference(instantiation,[status(thm)],[c_1480])).

cnf(c_2765,plain,
    ( X0_53 = sK6
    | X0_53 != sK7
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2627])).

cnf(c_2791,plain,
    ( sK6 != sK7
    | sK7 = sK6
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2765])).

cnf(c_2657,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1479])).

cnf(c_1483,plain,
    ( ~ m1_subset_1(X0_53,X0_54)
    | m1_subset_1(X1_53,X1_54)
    | X1_54 != X0_54
    | X1_53 != X0_53 ),
    theory(equality)).

cnf(c_2486,plain,
    ( m1_subset_1(X0_53,X0_54)
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | X0_54 != u1_struct_0(sK2)
    | X0_53 != sK7 ),
    inference(instantiation,[status(thm)],[c_1483])).

cnf(c_2608,plain,
    ( m1_subset_1(sK6,X0_54)
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | X0_54 != u1_struct_0(sK2)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2486])).

cnf(c_2656,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2608])).

cnf(c_1478,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_2614,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1478])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1472,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52)))
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X1_52)))
    | ~ l1_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2456,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1472])).

cnf(c_2602,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2456])).

cnf(c_5,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1471,plain,
    ( ~ v3_pre_topc(X0_53,X0_52)
    | v3_pre_topc(X0_53,X1_52)
    | ~ m1_pre_topc(X1_52,X0_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X1_52)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2511,plain,
    ( v3_pre_topc(sK5,X0_52)
    | ~ v3_pre_topc(sK5,sK1)
    | ~ m1_pre_topc(X0_52,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_2601,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ v3_pre_topc(sK5,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2511])).

cnf(c_12,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1467,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1497,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1478])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_209,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_732,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | u1_struct_0(sK2) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_209,c_13])).

cnf(c_733,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_11,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_15,negated_conjecture,
    ( v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4469,c_3988,c_3924,c_3559,c_3359,c_2919,c_2849,c_2839,c_2791,c_2657,c_2656,c_2614,c_2602,c_2601,c_1467,c_1497,c_733,c_10,c_11,c_13,c_15,c_16,c_17,c_18,c_19,c_20,c_23,c_24,c_26,c_27,c_28,c_29,c_30,c_31,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.31  % Computer   : n008.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 14:24:15 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 1.99/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/0.97  
% 1.99/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.99/0.97  
% 1.99/0.97  ------  iProver source info
% 1.99/0.97  
% 1.99/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.99/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.99/0.97  git: non_committed_changes: false
% 1.99/0.97  git: last_make_outside_of_git: false
% 1.99/0.97  
% 1.99/0.97  ------ 
% 1.99/0.97  
% 1.99/0.97  ------ Input Options
% 1.99/0.97  
% 1.99/0.97  --out_options                           all
% 1.99/0.97  --tptp_safe_out                         true
% 1.99/0.97  --problem_path                          ""
% 1.99/0.97  --include_path                          ""
% 1.99/0.97  --clausifier                            res/vclausify_rel
% 1.99/0.97  --clausifier_options                    --mode clausify
% 1.99/0.97  --stdin                                 false
% 1.99/0.97  --stats_out                             all
% 1.99/0.97  
% 1.99/0.97  ------ General Options
% 1.99/0.97  
% 1.99/0.97  --fof                                   false
% 1.99/0.97  --time_out_real                         305.
% 1.99/0.97  --time_out_virtual                      -1.
% 1.99/0.97  --symbol_type_check                     false
% 1.99/0.97  --clausify_out                          false
% 1.99/0.97  --sig_cnt_out                           false
% 1.99/0.97  --trig_cnt_out                          false
% 1.99/0.97  --trig_cnt_out_tolerance                1.
% 1.99/0.97  --trig_cnt_out_sk_spl                   false
% 1.99/0.97  --abstr_cl_out                          false
% 1.99/0.97  
% 1.99/0.97  ------ Global Options
% 1.99/0.97  
% 1.99/0.97  --schedule                              default
% 1.99/0.97  --add_important_lit                     false
% 1.99/0.97  --prop_solver_per_cl                    1000
% 1.99/0.97  --min_unsat_core                        false
% 1.99/0.97  --soft_assumptions                      false
% 1.99/0.97  --soft_lemma_size                       3
% 1.99/0.97  --prop_impl_unit_size                   0
% 1.99/0.97  --prop_impl_unit                        []
% 1.99/0.97  --share_sel_clauses                     true
% 1.99/0.97  --reset_solvers                         false
% 1.99/0.97  --bc_imp_inh                            [conj_cone]
% 1.99/0.97  --conj_cone_tolerance                   3.
% 1.99/0.97  --extra_neg_conj                        none
% 1.99/0.97  --large_theory_mode                     true
% 1.99/0.97  --prolific_symb_bound                   200
% 1.99/0.97  --lt_threshold                          2000
% 1.99/0.97  --clause_weak_htbl                      true
% 1.99/0.97  --gc_record_bc_elim                     false
% 1.99/0.97  
% 1.99/0.97  ------ Preprocessing Options
% 1.99/0.97  
% 1.99/0.97  --preprocessing_flag                    true
% 1.99/0.97  --time_out_prep_mult                    0.1
% 1.99/0.97  --splitting_mode                        input
% 1.99/0.97  --splitting_grd                         true
% 1.99/0.97  --splitting_cvd                         false
% 1.99/0.97  --splitting_cvd_svl                     false
% 1.99/0.97  --splitting_nvd                         32
% 1.99/0.97  --sub_typing                            true
% 1.99/0.97  --prep_gs_sim                           true
% 1.99/0.97  --prep_unflatten                        true
% 1.99/0.97  --prep_res_sim                          true
% 1.99/0.97  --prep_upred                            true
% 1.99/0.97  --prep_sem_filter                       exhaustive
% 1.99/0.97  --prep_sem_filter_out                   false
% 1.99/0.97  --pred_elim                             true
% 1.99/0.97  --res_sim_input                         true
% 1.99/0.97  --eq_ax_congr_red                       true
% 1.99/0.97  --pure_diseq_elim                       true
% 1.99/0.97  --brand_transform                       false
% 1.99/0.97  --non_eq_to_eq                          false
% 1.99/0.97  --prep_def_merge                        true
% 1.99/0.97  --prep_def_merge_prop_impl              false
% 1.99/0.97  --prep_def_merge_mbd                    true
% 1.99/0.97  --prep_def_merge_tr_red                 false
% 1.99/0.97  --prep_def_merge_tr_cl                  false
% 1.99/0.97  --smt_preprocessing                     true
% 1.99/0.97  --smt_ac_axioms                         fast
% 1.99/0.97  --preprocessed_out                      false
% 1.99/0.97  --preprocessed_stats                    false
% 1.99/0.97  
% 1.99/0.97  ------ Abstraction refinement Options
% 1.99/0.97  
% 1.99/0.97  --abstr_ref                             []
% 1.99/0.97  --abstr_ref_prep                        false
% 1.99/0.97  --abstr_ref_until_sat                   false
% 1.99/0.97  --abstr_ref_sig_restrict                funpre
% 1.99/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/0.97  --abstr_ref_under                       []
% 1.99/0.97  
% 1.99/0.97  ------ SAT Options
% 1.99/0.97  
% 1.99/0.97  --sat_mode                              false
% 1.99/0.97  --sat_fm_restart_options                ""
% 1.99/0.97  --sat_gr_def                            false
% 1.99/0.97  --sat_epr_types                         true
% 1.99/0.97  --sat_non_cyclic_types                  false
% 1.99/0.97  --sat_finite_models                     false
% 1.99/0.97  --sat_fm_lemmas                         false
% 1.99/0.97  --sat_fm_prep                           false
% 1.99/0.97  --sat_fm_uc_incr                        true
% 1.99/0.97  --sat_out_model                         small
% 1.99/0.97  --sat_out_clauses                       false
% 1.99/0.97  
% 1.99/0.97  ------ QBF Options
% 1.99/0.97  
% 1.99/0.97  --qbf_mode                              false
% 1.99/0.97  --qbf_elim_univ                         false
% 1.99/0.97  --qbf_dom_inst                          none
% 1.99/0.97  --qbf_dom_pre_inst                      false
% 1.99/0.97  --qbf_sk_in                             false
% 1.99/0.97  --qbf_pred_elim                         true
% 1.99/0.97  --qbf_split                             512
% 1.99/0.97  
% 1.99/0.97  ------ BMC1 Options
% 1.99/0.97  
% 1.99/0.97  --bmc1_incremental                      false
% 1.99/0.97  --bmc1_axioms                           reachable_all
% 1.99/0.97  --bmc1_min_bound                        0
% 1.99/0.97  --bmc1_max_bound                        -1
% 1.99/0.97  --bmc1_max_bound_default                -1
% 1.99/0.97  --bmc1_symbol_reachability              true
% 1.99/0.97  --bmc1_property_lemmas                  false
% 1.99/0.97  --bmc1_k_induction                      false
% 1.99/0.97  --bmc1_non_equiv_states                 false
% 1.99/0.97  --bmc1_deadlock                         false
% 1.99/0.97  --bmc1_ucm                              false
% 1.99/0.97  --bmc1_add_unsat_core                   none
% 1.99/0.97  --bmc1_unsat_core_children              false
% 1.99/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/0.97  --bmc1_out_stat                         full
% 1.99/0.97  --bmc1_ground_init                      false
% 1.99/0.97  --bmc1_pre_inst_next_state              false
% 1.99/0.97  --bmc1_pre_inst_state                   false
% 1.99/0.97  --bmc1_pre_inst_reach_state             false
% 1.99/0.97  --bmc1_out_unsat_core                   false
% 1.99/0.97  --bmc1_aig_witness_out                  false
% 1.99/0.97  --bmc1_verbose                          false
% 1.99/0.97  --bmc1_dump_clauses_tptp                false
% 1.99/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.99/0.97  --bmc1_dump_file                        -
% 1.99/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.99/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.99/0.97  --bmc1_ucm_extend_mode                  1
% 1.99/0.97  --bmc1_ucm_init_mode                    2
% 1.99/0.97  --bmc1_ucm_cone_mode                    none
% 1.99/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.99/0.97  --bmc1_ucm_relax_model                  4
% 1.99/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.99/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/0.97  --bmc1_ucm_layered_model                none
% 1.99/0.97  --bmc1_ucm_max_lemma_size               10
% 1.99/0.97  
% 1.99/0.97  ------ AIG Options
% 1.99/0.97  
% 1.99/0.97  --aig_mode                              false
% 1.99/0.97  
% 1.99/0.97  ------ Instantiation Options
% 1.99/0.97  
% 1.99/0.97  --instantiation_flag                    true
% 1.99/0.97  --inst_sos_flag                         false
% 1.99/0.97  --inst_sos_phase                        true
% 1.99/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/0.97  --inst_lit_sel_side                     num_symb
% 1.99/0.97  --inst_solver_per_active                1400
% 1.99/0.97  --inst_solver_calls_frac                1.
% 1.99/0.97  --inst_passive_queue_type               priority_queues
% 1.99/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/0.97  --inst_passive_queues_freq              [25;2]
% 1.99/0.97  --inst_dismatching                      true
% 1.99/0.97  --inst_eager_unprocessed_to_passive     true
% 1.99/0.97  --inst_prop_sim_given                   true
% 1.99/0.97  --inst_prop_sim_new                     false
% 1.99/0.97  --inst_subs_new                         false
% 1.99/0.97  --inst_eq_res_simp                      false
% 1.99/0.97  --inst_subs_given                       false
% 1.99/0.97  --inst_orphan_elimination               true
% 1.99/0.97  --inst_learning_loop_flag               true
% 1.99/0.97  --inst_learning_start                   3000
% 1.99/0.97  --inst_learning_factor                  2
% 1.99/0.97  --inst_start_prop_sim_after_learn       3
% 1.99/0.97  --inst_sel_renew                        solver
% 1.99/0.97  --inst_lit_activity_flag                true
% 1.99/0.97  --inst_restr_to_given                   false
% 1.99/0.97  --inst_activity_threshold               500
% 1.99/0.97  --inst_out_proof                        true
% 1.99/0.97  
% 1.99/0.97  ------ Resolution Options
% 1.99/0.97  
% 1.99/0.97  --resolution_flag                       true
% 1.99/0.97  --res_lit_sel                           adaptive
% 1.99/0.97  --res_lit_sel_side                      none
% 1.99/0.97  --res_ordering                          kbo
% 1.99/0.97  --res_to_prop_solver                    active
% 1.99/0.97  --res_prop_simpl_new                    false
% 1.99/0.97  --res_prop_simpl_given                  true
% 1.99/0.97  --res_passive_queue_type                priority_queues
% 1.99/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/0.97  --res_passive_queues_freq               [15;5]
% 1.99/0.97  --res_forward_subs                      full
% 1.99/0.97  --res_backward_subs                     full
% 1.99/0.97  --res_forward_subs_resolution           true
% 1.99/0.97  --res_backward_subs_resolution          true
% 1.99/0.97  --res_orphan_elimination                true
% 1.99/0.97  --res_time_limit                        2.
% 1.99/0.97  --res_out_proof                         true
% 1.99/0.97  
% 1.99/0.97  ------ Superposition Options
% 1.99/0.97  
% 1.99/0.97  --superposition_flag                    true
% 1.99/0.97  --sup_passive_queue_type                priority_queues
% 1.99/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.99/0.97  --demod_completeness_check              fast
% 1.99/0.97  --demod_use_ground                      true
% 1.99/0.97  --sup_to_prop_solver                    passive
% 1.99/0.97  --sup_prop_simpl_new                    true
% 1.99/0.97  --sup_prop_simpl_given                  true
% 1.99/0.97  --sup_fun_splitting                     false
% 1.99/0.97  --sup_smt_interval                      50000
% 1.99/0.97  
% 1.99/0.97  ------ Superposition Simplification Setup
% 1.99/0.97  
% 1.99/0.97  --sup_indices_passive                   []
% 1.99/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.97  --sup_full_bw                           [BwDemod]
% 1.99/0.97  --sup_immed_triv                        [TrivRules]
% 1.99/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.97  --sup_immed_bw_main                     []
% 1.99/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.97  
% 1.99/0.97  ------ Combination Options
% 1.99/0.97  
% 1.99/0.97  --comb_res_mult                         3
% 1.99/0.97  --comb_sup_mult                         2
% 1.99/0.97  --comb_inst_mult                        10
% 1.99/0.97  
% 1.99/0.97  ------ Debug Options
% 1.99/0.97  
% 1.99/0.97  --dbg_backtrace                         false
% 1.99/0.97  --dbg_dump_prop_clauses                 false
% 1.99/0.97  --dbg_dump_prop_clauses_file            -
% 1.99/0.97  --dbg_out_stat                          false
% 1.99/0.97  ------ Parsing...
% 1.99/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.99/0.97  
% 1.99/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.99/0.97  
% 1.99/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.99/0.97  
% 1.99/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.99/0.97  ------ Proving...
% 1.99/0.97  ------ Problem Properties 
% 1.99/0.97  
% 1.99/0.97  
% 1.99/0.97  clauses                                 29
% 1.99/0.97  conjectures                             20
% 1.99/0.97  EPR                                     16
% 1.99/0.97  Horn                                    26
% 1.99/0.97  unary                                   18
% 1.99/0.97  binary                                  4
% 1.99/0.97  lits                                    88
% 1.99/0.97  lits eq                                 5
% 1.99/0.97  fd_pure                                 0
% 1.99/0.97  fd_pseudo                               0
% 1.99/0.97  fd_cond                                 0
% 1.99/0.97  fd_pseudo_cond                          0
% 1.99/0.97  AC symbols                              0
% 1.99/0.97  
% 1.99/0.97  ------ Schedule dynamic 5 is on 
% 1.99/0.97  
% 1.99/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.99/0.97  
% 1.99/0.97  
% 1.99/0.97  ------ 
% 1.99/0.97  Current options:
% 1.99/0.97  ------ 
% 1.99/0.97  
% 1.99/0.97  ------ Input Options
% 1.99/0.97  
% 1.99/0.97  --out_options                           all
% 1.99/0.97  --tptp_safe_out                         true
% 1.99/0.97  --problem_path                          ""
% 1.99/0.97  --include_path                          ""
% 1.99/0.97  --clausifier                            res/vclausify_rel
% 1.99/0.97  --clausifier_options                    --mode clausify
% 1.99/0.97  --stdin                                 false
% 1.99/0.97  --stats_out                             all
% 1.99/0.97  
% 1.99/0.97  ------ General Options
% 1.99/0.97  
% 1.99/0.97  --fof                                   false
% 1.99/0.97  --time_out_real                         305.
% 1.99/0.97  --time_out_virtual                      -1.
% 1.99/0.97  --symbol_type_check                     false
% 1.99/0.97  --clausify_out                          false
% 1.99/0.97  --sig_cnt_out                           false
% 1.99/0.97  --trig_cnt_out                          false
% 1.99/0.97  --trig_cnt_out_tolerance                1.
% 1.99/0.97  --trig_cnt_out_sk_spl                   false
% 1.99/0.97  --abstr_cl_out                          false
% 1.99/0.97  
% 1.99/0.97  ------ Global Options
% 1.99/0.97  
% 1.99/0.97  --schedule                              default
% 1.99/0.97  --add_important_lit                     false
% 1.99/0.97  --prop_solver_per_cl                    1000
% 1.99/0.97  --min_unsat_core                        false
% 1.99/0.97  --soft_assumptions                      false
% 1.99/0.97  --soft_lemma_size                       3
% 1.99/0.97  --prop_impl_unit_size                   0
% 1.99/0.97  --prop_impl_unit                        []
% 1.99/0.97  --share_sel_clauses                     true
% 1.99/0.97  --reset_solvers                         false
% 1.99/0.97  --bc_imp_inh                            [conj_cone]
% 1.99/0.97  --conj_cone_tolerance                   3.
% 1.99/0.97  --extra_neg_conj                        none
% 1.99/0.97  --large_theory_mode                     true
% 1.99/0.97  --prolific_symb_bound                   200
% 1.99/0.97  --lt_threshold                          2000
% 1.99/0.97  --clause_weak_htbl                      true
% 1.99/0.97  --gc_record_bc_elim                     false
% 1.99/0.97  
% 1.99/0.97  ------ Preprocessing Options
% 1.99/0.97  
% 1.99/0.97  --preprocessing_flag                    true
% 1.99/0.97  --time_out_prep_mult                    0.1
% 1.99/0.97  --splitting_mode                        input
% 1.99/0.97  --splitting_grd                         true
% 1.99/0.97  --splitting_cvd                         false
% 1.99/0.97  --splitting_cvd_svl                     false
% 1.99/0.97  --splitting_nvd                         32
% 1.99/0.97  --sub_typing                            true
% 1.99/0.97  --prep_gs_sim                           true
% 1.99/0.97  --prep_unflatten                        true
% 1.99/0.97  --prep_res_sim                          true
% 1.99/0.97  --prep_upred                            true
% 1.99/0.97  --prep_sem_filter                       exhaustive
% 1.99/0.97  --prep_sem_filter_out                   false
% 1.99/0.97  --pred_elim                             true
% 1.99/0.97  --res_sim_input                         true
% 1.99/0.97  --eq_ax_congr_red                       true
% 1.99/0.97  --pure_diseq_elim                       true
% 1.99/0.97  --brand_transform                       false
% 1.99/0.97  --non_eq_to_eq                          false
% 1.99/0.97  --prep_def_merge                        true
% 1.99/0.97  --prep_def_merge_prop_impl              false
% 1.99/0.97  --prep_def_merge_mbd                    true
% 1.99/0.97  --prep_def_merge_tr_red                 false
% 1.99/0.97  --prep_def_merge_tr_cl                  false
% 1.99/0.97  --smt_preprocessing                     true
% 1.99/0.97  --smt_ac_axioms                         fast
% 1.99/0.97  --preprocessed_out                      false
% 1.99/0.97  --preprocessed_stats                    false
% 1.99/0.97  
% 1.99/0.97  ------ Abstraction refinement Options
% 1.99/0.97  
% 1.99/0.97  --abstr_ref                             []
% 1.99/0.97  --abstr_ref_prep                        false
% 1.99/0.97  --abstr_ref_until_sat                   false
% 1.99/0.97  --abstr_ref_sig_restrict                funpre
% 1.99/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/0.97  --abstr_ref_under                       []
% 1.99/0.97  
% 1.99/0.97  ------ SAT Options
% 1.99/0.97  
% 1.99/0.97  --sat_mode                              false
% 1.99/0.97  --sat_fm_restart_options                ""
% 1.99/0.97  --sat_gr_def                            false
% 1.99/0.97  --sat_epr_types                         true
% 1.99/0.97  --sat_non_cyclic_types                  false
% 1.99/0.97  --sat_finite_models                     false
% 1.99/0.97  --sat_fm_lemmas                         false
% 1.99/0.97  --sat_fm_prep                           false
% 1.99/0.97  --sat_fm_uc_incr                        true
% 1.99/0.97  --sat_out_model                         small
% 1.99/0.97  --sat_out_clauses                       false
% 1.99/0.97  
% 1.99/0.97  ------ QBF Options
% 1.99/0.97  
% 1.99/0.97  --qbf_mode                              false
% 1.99/0.97  --qbf_elim_univ                         false
% 1.99/0.97  --qbf_dom_inst                          none
% 1.99/0.97  --qbf_dom_pre_inst                      false
% 1.99/0.97  --qbf_sk_in                             false
% 1.99/0.97  --qbf_pred_elim                         true
% 1.99/0.97  --qbf_split                             512
% 1.99/0.97  
% 1.99/0.97  ------ BMC1 Options
% 1.99/0.97  
% 1.99/0.97  --bmc1_incremental                      false
% 1.99/0.97  --bmc1_axioms                           reachable_all
% 1.99/0.97  --bmc1_min_bound                        0
% 1.99/0.97  --bmc1_max_bound                        -1
% 1.99/0.97  --bmc1_max_bound_default                -1
% 1.99/0.97  --bmc1_symbol_reachability              true
% 1.99/0.97  --bmc1_property_lemmas                  false
% 1.99/0.97  --bmc1_k_induction                      false
% 1.99/0.97  --bmc1_non_equiv_states                 false
% 1.99/0.97  --bmc1_deadlock                         false
% 1.99/0.97  --bmc1_ucm                              false
% 1.99/0.97  --bmc1_add_unsat_core                   none
% 1.99/0.97  --bmc1_unsat_core_children              false
% 1.99/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/0.97  --bmc1_out_stat                         full
% 1.99/0.97  --bmc1_ground_init                      false
% 1.99/0.97  --bmc1_pre_inst_next_state              false
% 1.99/0.97  --bmc1_pre_inst_state                   false
% 1.99/0.97  --bmc1_pre_inst_reach_state             false
% 1.99/0.97  --bmc1_out_unsat_core                   false
% 1.99/0.97  --bmc1_aig_witness_out                  false
% 1.99/0.97  --bmc1_verbose                          false
% 1.99/0.97  --bmc1_dump_clauses_tptp                false
% 1.99/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.99/0.97  --bmc1_dump_file                        -
% 1.99/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.99/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.99/0.97  --bmc1_ucm_extend_mode                  1
% 1.99/0.97  --bmc1_ucm_init_mode                    2
% 1.99/0.97  --bmc1_ucm_cone_mode                    none
% 1.99/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.99/0.97  --bmc1_ucm_relax_model                  4
% 1.99/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.99/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/0.97  --bmc1_ucm_layered_model                none
% 1.99/0.97  --bmc1_ucm_max_lemma_size               10
% 1.99/0.97  
% 1.99/0.97  ------ AIG Options
% 1.99/0.97  
% 1.99/0.97  --aig_mode                              false
% 1.99/0.97  
% 1.99/0.97  ------ Instantiation Options
% 1.99/0.97  
% 1.99/0.97  --instantiation_flag                    true
% 1.99/0.97  --inst_sos_flag                         false
% 1.99/0.97  --inst_sos_phase                        true
% 1.99/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/0.97  --inst_lit_sel_side                     none
% 1.99/0.97  --inst_solver_per_active                1400
% 1.99/0.97  --inst_solver_calls_frac                1.
% 1.99/0.97  --inst_passive_queue_type               priority_queues
% 1.99/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/0.97  --inst_passive_queues_freq              [25;2]
% 1.99/0.97  --inst_dismatching                      true
% 1.99/0.97  --inst_eager_unprocessed_to_passive     true
% 1.99/0.97  --inst_prop_sim_given                   true
% 1.99/0.97  --inst_prop_sim_new                     false
% 1.99/0.97  --inst_subs_new                         false
% 1.99/0.97  --inst_eq_res_simp                      false
% 1.99/0.97  --inst_subs_given                       false
% 1.99/0.97  --inst_orphan_elimination               true
% 1.99/0.97  --inst_learning_loop_flag               true
% 1.99/0.97  --inst_learning_start                   3000
% 1.99/0.97  --inst_learning_factor                  2
% 1.99/0.97  --inst_start_prop_sim_after_learn       3
% 1.99/0.97  --inst_sel_renew                        solver
% 1.99/0.97  --inst_lit_activity_flag                true
% 1.99/0.97  --inst_restr_to_given                   false
% 1.99/0.97  --inst_activity_threshold               500
% 1.99/0.97  --inst_out_proof                        true
% 1.99/0.97  
% 1.99/0.97  ------ Resolution Options
% 1.99/0.97  
% 1.99/0.97  --resolution_flag                       false
% 1.99/0.97  --res_lit_sel                           adaptive
% 1.99/0.97  --res_lit_sel_side                      none
% 1.99/0.97  --res_ordering                          kbo
% 1.99/0.97  --res_to_prop_solver                    active
% 1.99/0.97  --res_prop_simpl_new                    false
% 1.99/0.97  --res_prop_simpl_given                  true
% 1.99/0.97  --res_passive_queue_type                priority_queues
% 1.99/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/0.97  --res_passive_queues_freq               [15;5]
% 1.99/0.97  --res_forward_subs                      full
% 1.99/0.97  --res_backward_subs                     full
% 1.99/0.97  --res_forward_subs_resolution           true
% 1.99/0.97  --res_backward_subs_resolution          true
% 1.99/0.97  --res_orphan_elimination                true
% 1.99/0.97  --res_time_limit                        2.
% 1.99/0.97  --res_out_proof                         true
% 1.99/0.97  
% 1.99/0.97  ------ Superposition Options
% 1.99/0.97  
% 1.99/0.97  --superposition_flag                    true
% 1.99/0.97  --sup_passive_queue_type                priority_queues
% 1.99/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.99/0.97  --demod_completeness_check              fast
% 1.99/0.97  --demod_use_ground                      true
% 1.99/0.97  --sup_to_prop_solver                    passive
% 1.99/0.97  --sup_prop_simpl_new                    true
% 1.99/0.97  --sup_prop_simpl_given                  true
% 1.99/0.97  --sup_fun_splitting                     false
% 1.99/0.97  --sup_smt_interval                      50000
% 1.99/0.97  
% 1.99/0.97  ------ Superposition Simplification Setup
% 1.99/0.97  
% 1.99/0.97  --sup_indices_passive                   []
% 1.99/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.97  --sup_full_bw                           [BwDemod]
% 1.99/0.97  --sup_immed_triv                        [TrivRules]
% 1.99/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.97  --sup_immed_bw_main                     []
% 1.99/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.97  
% 1.99/0.97  ------ Combination Options
% 1.99/0.97  
% 1.99/0.97  --comb_res_mult                         3
% 1.99/0.97  --comb_sup_mult                         2
% 1.99/0.97  --comb_inst_mult                        10
% 1.99/0.97  
% 1.99/0.97  ------ Debug Options
% 1.99/0.97  
% 1.99/0.97  --dbg_backtrace                         false
% 1.99/0.97  --dbg_dump_prop_clauses                 false
% 1.99/0.97  --dbg_dump_prop_clauses_file            -
% 1.99/0.97  --dbg_out_stat                          false
% 1.99/0.97  
% 1.99/0.97  
% 1.99/0.97  
% 1.99/0.97  
% 1.99/0.97  ------ Proving...
% 1.99/0.97  
% 1.99/0.97  
% 1.99/0.97  % SZS status Theorem for theBenchmark.p
% 1.99/0.97  
% 1.99/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 1.99/0.97  
% 1.99/0.97  fof(f6,axiom,(
% 1.99/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f17,plain,(
% 1.99/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.99/0.97    inference(ennf_transformation,[],[f6])).
% 1.99/0.97  
% 1.99/0.97  fof(f18,plain,(
% 1.99/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.99/0.97    inference(flattening,[],[f17])).
% 1.99/0.97  
% 1.99/0.97  fof(f44,plain,(
% 1.99/0.97    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.99/0.97    inference(cnf_transformation,[],[f18])).
% 1.99/0.97  
% 1.99/0.97  fof(f9,conjecture,(
% 1.99/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f10,negated_conjecture,(
% 1.99/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 1.99/0.97    inference(negated_conjecture,[],[f9])).
% 1.99/0.97  
% 1.99/0.97  fof(f23,plain,(
% 1.99/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.99/0.97    inference(ennf_transformation,[],[f10])).
% 1.99/0.97  
% 1.99/0.97  fof(f24,plain,(
% 1.99/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.99/0.97    inference(flattening,[],[f23])).
% 1.99/0.97  
% 1.99/0.97  fof(f27,plain,(
% 1.99/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.99/0.97    inference(nnf_transformation,[],[f24])).
% 1.99/0.97  
% 1.99/0.97  fof(f28,plain,(
% 1.99/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.99/0.97    inference(flattening,[],[f27])).
% 1.99/0.97  
% 1.99/0.97  fof(f36,plain,(
% 1.99/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | r1_tmap_1(X3,X0,X4,X6)) & sK7 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 1.99/0.97    introduced(choice_axiom,[])).
% 1.99/0.97  
% 1.99/0.97  fof(f35,plain,(
% 1.99/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,sK6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,sK6)) & sK6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 1.99/0.97    introduced(choice_axiom,[])).
% 1.99/0.97  
% 1.99/0.97  fof(f34,plain,(
% 1.99/0.97    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(X2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 1.99/0.97    introduced(choice_axiom,[])).
% 1.99/0.97  
% 1.99/0.97  fof(f33,plain,(
% 1.99/0.97    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7) | ~r1_tmap_1(X3,X0,sK4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7) | r1_tmap_1(X3,X0,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 1.99/0.97    introduced(choice_axiom,[])).
% 1.99/0.97  
% 1.99/0.97  fof(f32,plain,(
% 1.99/0.97    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7) | ~r1_tmap_1(sK3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7) | r1_tmap_1(sK3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 1.99/0.97    introduced(choice_axiom,[])).
% 1.99/0.97  
% 1.99/0.97  fof(f31,plain,(
% 1.99/0.97    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 1.99/0.97    introduced(choice_axiom,[])).
% 1.99/0.97  
% 1.99/0.97  fof(f30,plain,(
% 1.99/0.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.99/0.97    introduced(choice_axiom,[])).
% 1.99/0.97  
% 1.99/0.97  fof(f29,plain,(
% 1.99/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.99/0.97    introduced(choice_axiom,[])).
% 1.99/0.97  
% 1.99/0.97  fof(f37,plain,(
% 1.99/0.97    ((((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.99/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f28,f36,f35,f34,f33,f32,f31,f30,f29])).
% 1.99/0.97  
% 1.99/0.97  fof(f66,plain,(
% 1.99/0.97    r2_hidden(sK6,sK5)),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f8,axiom,(
% 1.99/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f21,plain,(
% 1.99/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.99/0.97    inference(ennf_transformation,[],[f8])).
% 1.99/0.97  
% 1.99/0.97  fof(f22,plain,(
% 1.99/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.99/0.97    inference(flattening,[],[f21])).
% 1.99/0.97  
% 1.99/0.97  fof(f26,plain,(
% 1.99/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.99/0.97    inference(nnf_transformation,[],[f22])).
% 1.99/0.97  
% 1.99/0.97  fof(f46,plain,(
% 1.99/0.97    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.99/0.97    inference(cnf_transformation,[],[f26])).
% 1.99/0.97  
% 1.99/0.97  fof(f73,plain,(
% 1.99/0.97    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.99/0.97    inference(equality_resolution,[],[f46])).
% 1.99/0.97  
% 1.99/0.97  fof(f59,plain,(
% 1.99/0.97    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f58,plain,(
% 1.99/0.97    v1_funct_1(sK4)),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f7,axiom,(
% 1.99/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f19,plain,(
% 1.99/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.99/0.97    inference(ennf_transformation,[],[f7])).
% 1.99/0.97  
% 1.99/0.97  fof(f20,plain,(
% 1.99/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.99/0.97    inference(flattening,[],[f19])).
% 1.99/0.97  
% 1.99/0.97  fof(f45,plain,(
% 1.99/0.97    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.99/0.97    inference(cnf_transformation,[],[f20])).
% 1.99/0.97  
% 1.99/0.97  fof(f2,axiom,(
% 1.99/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f11,plain,(
% 1.99/0.97    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.99/0.97    inference(ennf_transformation,[],[f2])).
% 1.99/0.97  
% 1.99/0.97  fof(f12,plain,(
% 1.99/0.97    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.99/0.97    inference(flattening,[],[f11])).
% 1.99/0.97  
% 1.99/0.97  fof(f40,plain,(
% 1.99/0.97    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.99/0.97    inference(cnf_transformation,[],[f12])).
% 1.99/0.97  
% 1.99/0.97  fof(f3,axiom,(
% 1.99/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f13,plain,(
% 1.99/0.97    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.99/0.97    inference(ennf_transformation,[],[f3])).
% 1.99/0.97  
% 1.99/0.97  fof(f41,plain,(
% 1.99/0.97    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.99/0.97    inference(cnf_transformation,[],[f13])).
% 1.99/0.97  
% 1.99/0.97  fof(f47,plain,(
% 1.99/0.97    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.99/0.97    inference(cnf_transformation,[],[f26])).
% 1.99/0.97  
% 1.99/0.97  fof(f72,plain,(
% 1.99/0.97    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.99/0.97    inference(equality_resolution,[],[f47])).
% 1.99/0.97  
% 1.99/0.97  fof(f4,axiom,(
% 1.99/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f14,plain,(
% 1.99/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.99/0.97    inference(ennf_transformation,[],[f4])).
% 1.99/0.97  
% 1.99/0.97  fof(f42,plain,(
% 1.99/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.99/0.97    inference(cnf_transformation,[],[f14])).
% 1.99/0.97  
% 1.99/0.97  fof(f5,axiom,(
% 1.99/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f15,plain,(
% 1.99/0.97    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.99/0.97    inference(ennf_transformation,[],[f5])).
% 1.99/0.97  
% 1.99/0.97  fof(f16,plain,(
% 1.99/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.99/0.97    inference(flattening,[],[f15])).
% 1.99/0.97  
% 1.99/0.97  fof(f43,plain,(
% 1.99/0.97    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.99/0.97    inference(cnf_transformation,[],[f16])).
% 1.99/0.97  
% 1.99/0.97  fof(f71,plain,(
% 1.99/0.97    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.99/0.97    inference(equality_resolution,[],[f43])).
% 1.99/0.97  
% 1.99/0.97  fof(f68,plain,(
% 1.99/0.97    sK6 = sK7),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f1,axiom,(
% 1.99/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.97  
% 1.99/0.97  fof(f25,plain,(
% 1.99/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.99/0.97    inference(nnf_transformation,[],[f1])).
% 1.99/0.97  
% 1.99/0.97  fof(f39,plain,(
% 1.99/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.99/0.97    inference(cnf_transformation,[],[f25])).
% 1.99/0.97  
% 1.99/0.97  fof(f67,plain,(
% 1.99/0.97    r1_tarski(sK5,u1_struct_0(sK2))),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f70,plain,(
% 1.99/0.97    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f69,plain,(
% 1.99/0.97    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f65,plain,(
% 1.99/0.97    v3_pre_topc(sK5,sK1)),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f64,plain,(
% 1.99/0.97    m1_subset_1(sK7,u1_struct_0(sK2))),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f63,plain,(
% 1.99/0.97    m1_subset_1(sK6,u1_struct_0(sK3))),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f62,plain,(
% 1.99/0.97    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f61,plain,(
% 1.99/0.97    m1_pre_topc(sK2,sK3)),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f60,plain,(
% 1.99/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f57,plain,(
% 1.99/0.97    m1_pre_topc(sK3,sK1)),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f56,plain,(
% 1.99/0.97    ~v2_struct_0(sK3)),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f54,plain,(
% 1.99/0.97    ~v2_struct_0(sK2)),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f53,plain,(
% 1.99/0.97    l1_pre_topc(sK1)),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f52,plain,(
% 1.99/0.97    v2_pre_topc(sK1)),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f51,plain,(
% 1.99/0.97    ~v2_struct_0(sK1)),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f50,plain,(
% 1.99/0.97    l1_pre_topc(sK0)),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f49,plain,(
% 1.99/0.97    v2_pre_topc(sK0)),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  fof(f48,plain,(
% 1.99/0.97    ~v2_struct_0(sK0)),
% 1.99/0.97    inference(cnf_transformation,[],[f37])).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1486,plain,
% 1.99/0.97      ( ~ r1_tmap_1(X0_52,X1_52,X0_53,X1_53)
% 1.99/0.97      | r1_tmap_1(X0_52,X1_52,X2_53,X3_53)
% 1.99/0.97      | X2_53 != X0_53
% 1.99/0.97      | X3_53 != X1_53 ),
% 1.99/0.97      theory(equality) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2782,plain,
% 1.99/0.97      ( r1_tmap_1(sK2,sK0,X0_53,X1_53)
% 1.99/0.97      | ~ r1_tmap_1(sK2,sK0,X2_53,sK6)
% 1.99/0.97      | X0_53 != X2_53
% 1.99/0.97      | X1_53 != sK6 ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_1486]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_3119,plain,
% 1.99/0.97      ( ~ r1_tmap_1(sK2,sK0,X0_53,sK6)
% 1.99/0.97      | r1_tmap_1(sK2,sK0,X1_53,sK7)
% 1.99/0.97      | X1_53 != X0_53
% 1.99/0.97      | sK7 != sK6 ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_2782]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_3607,plain,
% 1.99/0.97      ( r1_tmap_1(sK2,sK0,X0_53,sK7)
% 1.99/0.97      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X1_53),sK6)
% 1.99/0.97      | X0_53 != k3_tmap_1(sK1,sK0,sK3,sK2,X1_53)
% 1.99/0.97      | sK7 != sK6 ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_3119]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_4469,plain,
% 1.99/0.97      ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 1.99/0.97      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 1.99/0.97      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 1.99/0.97      | sK7 != sK6 ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_3607]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_6,plain,
% 1.99/0.97      ( m1_connsp_2(X0,X1,X2)
% 1.99/0.97      | ~ r2_hidden(X2,X0)
% 1.99/0.97      | ~ v3_pre_topc(X0,X1)
% 1.99/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.99/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X1) ),
% 1.99/0.97      inference(cnf_transformation,[],[f44]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_14,negated_conjecture,
% 1.99/0.97      ( r2_hidden(sK6,sK5) ),
% 1.99/0.97      inference(cnf_transformation,[],[f66]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_400,plain,
% 1.99/0.97      ( m1_connsp_2(X0,X1,X2)
% 1.99/0.97      | ~ v3_pre_topc(X0,X1)
% 1.99/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.99/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | sK5 != X0
% 1.99/0.97      | sK6 != X2 ),
% 1.99/0.97      inference(resolution_lifted,[status(thm)],[c_6,c_14]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_401,plain,
% 1.99/0.97      ( m1_connsp_2(sK5,X0,sK6)
% 1.99/0.97      | ~ v3_pre_topc(sK5,X0)
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | ~ l1_pre_topc(X0)
% 1.99/0.97      | ~ v2_pre_topc(X0) ),
% 1.99/0.97      inference(unflattening,[status(thm)],[c_400]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_9,plain,
% 1.99/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.99/0.97      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.99/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.99/0.97      | ~ m1_connsp_2(X6,X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X4,X5)
% 1.99/0.97      | ~ m1_pre_topc(X4,X0)
% 1.99/0.97      | ~ m1_pre_topc(X0,X5)
% 1.99/0.97      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.99/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.99/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.99/0.97      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.99/0.97      | ~ v1_funct_1(X2)
% 1.99/0.97      | v2_struct_0(X5)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X4)
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | ~ l1_pre_topc(X5)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X5)
% 1.99/0.97      | ~ v2_pre_topc(X1) ),
% 1.99/0.97      inference(cnf_transformation,[],[f73]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_21,negated_conjecture,
% 1.99/0.97      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
% 1.99/0.97      inference(cnf_transformation,[],[f59]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_435,plain,
% 1.99/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.99/0.97      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.99/0.97      | ~ m1_connsp_2(X6,X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X4,X5)
% 1.99/0.97      | ~ m1_pre_topc(X4,X0)
% 1.99/0.97      | ~ m1_pre_topc(X0,X5)
% 1.99/0.97      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.99/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.99/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.99/0.97      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.99/0.97      | ~ v1_funct_1(X2)
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X5)
% 1.99/0.97      | v2_struct_0(X4)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ l1_pre_topc(X5)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X5)
% 1.99/0.97      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.99/0.97      | sK4 != X2 ),
% 1.99/0.97      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_436,plain,
% 1.99/0.97      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.99/0.97      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.99/0.97      | ~ m1_connsp_2(X5,X3,X4)
% 1.99/0.97      | ~ m1_pre_topc(X0,X2)
% 1.99/0.97      | ~ m1_pre_topc(X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X3,X2)
% 1.99/0.97      | ~ r1_tarski(X5,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.99/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.99/0.97      | ~ v1_funct_1(sK4)
% 1.99/0.97      | v2_struct_0(X3)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X2)
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ l1_pre_topc(X2)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X2)
% 1.99/0.97      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.99/0.97      inference(unflattening,[status(thm)],[c_435]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_22,negated_conjecture,
% 1.99/0.97      ( v1_funct_1(sK4) ),
% 1.99/0.97      inference(cnf_transformation,[],[f58]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_440,plain,
% 1.99/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.99/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.99/0.97      | ~ r1_tarski(X5,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_pre_topc(X3,X2)
% 1.99/0.97      | ~ m1_pre_topc(X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X0,X2)
% 1.99/0.97      | ~ m1_connsp_2(X5,X3,X4)
% 1.99/0.97      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.99/0.97      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.99/0.97      | v2_struct_0(X3)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X2)
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ l1_pre_topc(X2)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X2)
% 1.99/0.97      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.99/0.97      inference(global_propositional_subsumption,
% 1.99/0.97                [status(thm)],
% 1.99/0.97                [c_436,c_22]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_441,plain,
% 1.99/0.97      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.99/0.97      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.99/0.97      | ~ m1_connsp_2(X5,X3,X4)
% 1.99/0.97      | ~ m1_pre_topc(X0,X2)
% 1.99/0.97      | ~ m1_pre_topc(X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X3,X2)
% 1.99/0.97      | ~ r1_tarski(X5,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.99/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X2)
% 1.99/0.97      | v2_struct_0(X3)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ l1_pre_topc(X2)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X2)
% 1.99/0.97      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.99/0.97      inference(renaming,[status(thm)],[c_440]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_7,plain,
% 1.99/0.97      ( ~ m1_pre_topc(X0,X1)
% 1.99/0.97      | ~ m1_pre_topc(X2,X0)
% 1.99/0.97      | m1_pre_topc(X2,X1)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X1) ),
% 1.99/0.97      inference(cnf_transformation,[],[f45]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_488,plain,
% 1.99/0.97      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.99/0.97      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.99/0.97      | ~ m1_connsp_2(X5,X3,X4)
% 1.99/0.97      | ~ m1_pre_topc(X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X3,X2)
% 1.99/0.97      | ~ r1_tarski(X5,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.99/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X2)
% 1.99/0.97      | v2_struct_0(X3)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ l1_pre_topc(X2)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X2)
% 1.99/0.97      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.99/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_441,c_7]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_658,plain,
% 1.99/0.97      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.99/0.97      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.99/0.97      | ~ v3_pre_topc(sK5,X5)
% 1.99/0.97      | ~ m1_pre_topc(X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X3,X2)
% 1.99/0.97      | ~ r1_tarski(X6,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.99/0.97      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3)))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X5)))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(X5))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.99/0.97      | v2_struct_0(X5)
% 1.99/0.97      | v2_struct_0(X3)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | v2_struct_0(X2)
% 1.99/0.97      | ~ l1_pre_topc(X5)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ l1_pre_topc(X2)
% 1.99/0.97      | ~ v2_pre_topc(X5)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X2)
% 1.99/0.97      | X3 != X5
% 1.99/0.97      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.99/0.97      | sK5 != X6
% 1.99/0.97      | sK6 != X4 ),
% 1.99/0.97      inference(resolution_lifted,[status(thm)],[c_401,c_488]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_659,plain,
% 1.99/0.97      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 1.99/0.97      | ~ r1_tmap_1(X3,X1,sK4,sK6)
% 1.99/0.97      | ~ v3_pre_topc(sK5,X3)
% 1.99/0.97      | ~ m1_pre_topc(X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X3,X2)
% 1.99/0.97      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X2)
% 1.99/0.97      | v2_struct_0(X3)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ l1_pre_topc(X3)
% 1.99/0.97      | ~ l1_pre_topc(X2)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X3)
% 1.99/0.97      | ~ v2_pre_topc(X2)
% 1.99/0.97      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.99/0.97      inference(unflattening,[status(thm)],[c_658]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2,plain,
% 1.99/0.97      ( ~ m1_pre_topc(X0,X1)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | v2_pre_topc(X0) ),
% 1.99/0.97      inference(cnf_transformation,[],[f40]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_3,plain,
% 1.99/0.97      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.99/0.97      inference(cnf_transformation,[],[f41]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_707,plain,
% 1.99/0.97      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 1.99/0.97      | ~ r1_tmap_1(X3,X1,sK4,sK6)
% 1.99/0.97      | ~ v3_pre_topc(sK5,X3)
% 1.99/0.97      | ~ m1_pre_topc(X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X3,X2)
% 1.99/0.97      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X2)
% 1.99/0.97      | v2_struct_0(X3)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ l1_pre_topc(X2)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X2)
% 1.99/0.97      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.99/0.97      inference(forward_subsumption_resolution,
% 1.99/0.97                [status(thm)],
% 1.99/0.97                [c_659,c_2,c_3]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1448,plain,
% 1.99/0.97      ( r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,X3_52,X0_52,sK4),sK6)
% 1.99/0.97      | ~ r1_tmap_1(X3_52,X1_52,sK4,sK6)
% 1.99/0.97      | ~ v3_pre_topc(sK5,X3_52)
% 1.99/0.97      | ~ m1_pre_topc(X0_52,X3_52)
% 1.99/0.97      | ~ m1_pre_topc(X3_52,X2_52)
% 1.99/0.97      | ~ r1_tarski(sK5,u1_struct_0(X0_52))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_52)))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(X0_52))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(X3_52))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
% 1.99/0.97      | v2_struct_0(X0_52)
% 1.99/0.97      | v2_struct_0(X1_52)
% 1.99/0.97      | v2_struct_0(X2_52)
% 1.99/0.97      | v2_struct_0(X3_52)
% 1.99/0.97      | ~ l1_pre_topc(X1_52)
% 1.99/0.97      | ~ l1_pre_topc(X2_52)
% 1.99/0.97      | ~ v2_pre_topc(X1_52)
% 1.99/0.97      | ~ v2_pre_topc(X2_52)
% 1.99/0.97      | u1_struct_0(X3_52) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1_52) != u1_struct_0(sK0) ),
% 1.99/0.97      inference(subtyping,[status(esa)],[c_707]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_3004,plain,
% 1.99/0.97      ( r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,sK3,X0_52,sK4),sK6)
% 1.99/0.97      | ~ r1_tmap_1(sK3,X1_52,sK4,sK6)
% 1.99/0.97      | ~ v3_pre_topc(sK5,sK3)
% 1.99/0.97      | ~ m1_pre_topc(X0_52,sK3)
% 1.99/0.97      | ~ m1_pre_topc(sK3,X2_52)
% 1.99/0.97      | ~ r1_tarski(sK5,u1_struct_0(X0_52))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(X0_52))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_52))))
% 1.99/0.97      | v2_struct_0(X0_52)
% 1.99/0.97      | v2_struct_0(X1_52)
% 1.99/0.97      | v2_struct_0(X2_52)
% 1.99/0.97      | v2_struct_0(sK3)
% 1.99/0.97      | ~ l1_pre_topc(X1_52)
% 1.99/0.97      | ~ l1_pre_topc(X2_52)
% 1.99/0.97      | ~ v2_pre_topc(X1_52)
% 1.99/0.97      | ~ v2_pre_topc(X2_52)
% 1.99/0.97      | u1_struct_0(X1_52) != u1_struct_0(sK0)
% 1.99/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_1448]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_3382,plain,
% 1.99/0.97      ( ~ r1_tmap_1(sK3,X0_52,sK4,sK6)
% 1.99/0.97      | r1_tmap_1(sK2,X0_52,k3_tmap_1(X1_52,X0_52,sK3,sK2,sK4),sK6)
% 1.99/0.97      | ~ v3_pre_topc(sK5,sK3)
% 1.99/0.97      | ~ m1_pre_topc(sK3,X1_52)
% 1.99/0.97      | ~ m1_pre_topc(sK2,sK3)
% 1.99/0.97      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52))))
% 1.99/0.97      | v2_struct_0(X0_52)
% 1.99/0.97      | v2_struct_0(X1_52)
% 1.99/0.97      | v2_struct_0(sK3)
% 1.99/0.97      | v2_struct_0(sK2)
% 1.99/0.97      | ~ l1_pre_topc(X1_52)
% 1.99/0.97      | ~ l1_pre_topc(X0_52)
% 1.99/0.97      | ~ v2_pre_topc(X1_52)
% 1.99/0.97      | ~ v2_pre_topc(X0_52)
% 1.99/0.97      | u1_struct_0(X0_52) != u1_struct_0(sK0)
% 1.99/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_3004]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_3986,plain,
% 1.99/0.97      ( ~ r1_tmap_1(sK3,X0_52,sK4,sK6)
% 1.99/0.97      | r1_tmap_1(sK2,X0_52,k3_tmap_1(sK1,X0_52,sK3,sK2,sK4),sK6)
% 1.99/0.97      | ~ v3_pre_topc(sK5,sK3)
% 1.99/0.97      | ~ m1_pre_topc(sK3,sK1)
% 1.99/0.97      | ~ m1_pre_topc(sK2,sK3)
% 1.99/0.97      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52))))
% 1.99/0.97      | v2_struct_0(X0_52)
% 1.99/0.97      | v2_struct_0(sK3)
% 1.99/0.97      | v2_struct_0(sK1)
% 1.99/0.97      | v2_struct_0(sK2)
% 1.99/0.97      | ~ l1_pre_topc(X0_52)
% 1.99/0.97      | ~ l1_pre_topc(sK1)
% 1.99/0.97      | ~ v2_pre_topc(X0_52)
% 1.99/0.97      | ~ v2_pre_topc(sK1)
% 1.99/0.97      | u1_struct_0(X0_52) != u1_struct_0(sK0)
% 1.99/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_3382]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_3988,plain,
% 1.99/0.97      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 1.99/0.97      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 1.99/0.97      | ~ v3_pre_topc(sK5,sK3)
% 1.99/0.97      | ~ m1_pre_topc(sK3,sK1)
% 1.99/0.97      | ~ m1_pre_topc(sK2,sK3)
% 1.99/0.97      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
% 1.99/0.97      | v2_struct_0(sK3)
% 1.99/0.97      | v2_struct_0(sK1)
% 1.99/0.97      | v2_struct_0(sK0)
% 1.99/0.97      | v2_struct_0(sK2)
% 1.99/0.97      | ~ l1_pre_topc(sK1)
% 1.99/0.97      | ~ l1_pre_topc(sK0)
% 1.99/0.97      | ~ v2_pre_topc(sK1)
% 1.99/0.97      | ~ v2_pre_topc(sK0)
% 1.99/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_3986]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1479,plain,( X0_54 = X0_54 ),theory(equality) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_3924,plain,
% 1.99/0.97      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_1479]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_8,plain,
% 1.99/0.97      ( r1_tmap_1(X0,X1,X2,X3)
% 1.99/0.97      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.99/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.99/0.97      | ~ m1_connsp_2(X6,X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X4,X5)
% 1.99/0.97      | ~ m1_pre_topc(X4,X0)
% 1.99/0.97      | ~ m1_pre_topc(X0,X5)
% 1.99/0.97      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.99/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.99/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.99/0.97      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.99/0.97      | ~ v1_funct_1(X2)
% 1.99/0.97      | v2_struct_0(X5)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X4)
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | ~ l1_pre_topc(X5)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X5)
% 1.99/0.97      | ~ v2_pre_topc(X1) ),
% 1.99/0.97      inference(cnf_transformation,[],[f72]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_510,plain,
% 1.99/0.97      ( r1_tmap_1(X0,X1,X2,X3)
% 1.99/0.97      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.99/0.97      | ~ m1_connsp_2(X6,X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X4,X5)
% 1.99/0.97      | ~ m1_pre_topc(X4,X0)
% 1.99/0.97      | ~ m1_pre_topc(X0,X5)
% 1.99/0.97      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.99/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.99/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.99/0.97      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.99/0.97      | ~ v1_funct_1(X2)
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X5)
% 1.99/0.97      | v2_struct_0(X4)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ l1_pre_topc(X5)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X5)
% 1.99/0.97      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.99/0.97      | sK4 != X2 ),
% 1.99/0.97      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_511,plain,
% 1.99/0.97      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.99/0.97      | r1_tmap_1(X3,X1,sK4,X4)
% 1.99/0.97      | ~ m1_connsp_2(X5,X3,X4)
% 1.99/0.97      | ~ m1_pre_topc(X0,X2)
% 1.99/0.97      | ~ m1_pre_topc(X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X3,X2)
% 1.99/0.97      | ~ r1_tarski(X5,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.99/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.99/0.97      | ~ v1_funct_1(sK4)
% 1.99/0.97      | v2_struct_0(X3)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X2)
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ l1_pre_topc(X2)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X2)
% 1.99/0.97      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.99/0.97      inference(unflattening,[status(thm)],[c_510]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_515,plain,
% 1.99/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.99/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.99/0.97      | ~ r1_tarski(X5,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_pre_topc(X3,X2)
% 1.99/0.97      | ~ m1_pre_topc(X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X0,X2)
% 1.99/0.97      | ~ m1_connsp_2(X5,X3,X4)
% 1.99/0.97      | r1_tmap_1(X3,X1,sK4,X4)
% 1.99/0.97      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.99/0.97      | v2_struct_0(X3)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X2)
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ l1_pre_topc(X2)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X2)
% 1.99/0.97      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.99/0.97      inference(global_propositional_subsumption,
% 1.99/0.97                [status(thm)],
% 1.99/0.97                [c_511,c_22]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_516,plain,
% 1.99/0.97      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.99/0.97      | r1_tmap_1(X3,X1,sK4,X4)
% 1.99/0.97      | ~ m1_connsp_2(X5,X3,X4)
% 1.99/0.97      | ~ m1_pre_topc(X0,X2)
% 1.99/0.97      | ~ m1_pre_topc(X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X3,X2)
% 1.99/0.97      | ~ r1_tarski(X5,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.99/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X2)
% 1.99/0.97      | v2_struct_0(X3)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ l1_pre_topc(X2)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X2)
% 1.99/0.97      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.99/0.97      inference(renaming,[status(thm)],[c_515]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_563,plain,
% 1.99/0.97      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.99/0.97      | r1_tmap_1(X3,X1,sK4,X4)
% 1.99/0.97      | ~ m1_connsp_2(X5,X3,X4)
% 1.99/0.97      | ~ m1_pre_topc(X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X3,X2)
% 1.99/0.97      | ~ r1_tarski(X5,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.99/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X2)
% 1.99/0.97      | v2_struct_0(X3)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ l1_pre_topc(X2)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X2)
% 1.99/0.97      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.99/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_516,c_7]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_587,plain,
% 1.99/0.97      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.99/0.97      | r1_tmap_1(X3,X1,sK4,X4)
% 1.99/0.97      | ~ v3_pre_topc(sK5,X5)
% 1.99/0.97      | ~ m1_pre_topc(X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X3,X2)
% 1.99/0.97      | ~ r1_tarski(X6,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.99/0.97      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3)))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X5)))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(X5))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.99/0.97      | v2_struct_0(X5)
% 1.99/0.97      | v2_struct_0(X3)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | v2_struct_0(X2)
% 1.99/0.97      | ~ l1_pre_topc(X5)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ l1_pre_topc(X2)
% 1.99/0.97      | ~ v2_pre_topc(X5)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X2)
% 1.99/0.97      | X3 != X5
% 1.99/0.97      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.99/0.97      | sK5 != X6
% 1.99/0.97      | sK6 != X4 ),
% 1.99/0.97      inference(resolution_lifted,[status(thm)],[c_401,c_563]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_588,plain,
% 1.99/0.97      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 1.99/0.97      | r1_tmap_1(X3,X1,sK4,sK6)
% 1.99/0.97      | ~ v3_pre_topc(sK5,X3)
% 1.99/0.97      | ~ m1_pre_topc(X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X3,X2)
% 1.99/0.97      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X2)
% 1.99/0.97      | v2_struct_0(X3)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ l1_pre_topc(X3)
% 1.99/0.97      | ~ l1_pre_topc(X2)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X3)
% 1.99/0.97      | ~ v2_pre_topc(X2)
% 1.99/0.97      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.99/0.97      inference(unflattening,[status(thm)],[c_587]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_636,plain,
% 1.99/0.97      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 1.99/0.97      | r1_tmap_1(X3,X1,sK4,sK6)
% 1.99/0.97      | ~ v3_pre_topc(sK5,X3)
% 1.99/0.97      | ~ m1_pre_topc(X0,X3)
% 1.99/0.97      | ~ m1_pre_topc(X3,X2)
% 1.99/0.97      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.99/0.97      | v2_struct_0(X0)
% 1.99/0.97      | v2_struct_0(X1)
% 1.99/0.97      | v2_struct_0(X2)
% 1.99/0.97      | v2_struct_0(X3)
% 1.99/0.97      | ~ l1_pre_topc(X1)
% 1.99/0.97      | ~ l1_pre_topc(X2)
% 1.99/0.97      | ~ v2_pre_topc(X1)
% 1.99/0.97      | ~ v2_pre_topc(X2)
% 1.99/0.97      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.99/0.97      inference(forward_subsumption_resolution,
% 1.99/0.97                [status(thm)],
% 1.99/0.97                [c_588,c_2,c_3]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1449,plain,
% 1.99/0.97      ( ~ r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,X3_52,X0_52,sK4),sK6)
% 1.99/0.97      | r1_tmap_1(X3_52,X1_52,sK4,sK6)
% 1.99/0.97      | ~ v3_pre_topc(sK5,X3_52)
% 1.99/0.97      | ~ m1_pre_topc(X0_52,X3_52)
% 1.99/0.97      | ~ m1_pre_topc(X3_52,X2_52)
% 1.99/0.97      | ~ r1_tarski(sK5,u1_struct_0(X0_52))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_52)))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(X0_52))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(X3_52))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
% 1.99/0.97      | v2_struct_0(X0_52)
% 1.99/0.97      | v2_struct_0(X1_52)
% 1.99/0.97      | v2_struct_0(X2_52)
% 1.99/0.97      | v2_struct_0(X3_52)
% 1.99/0.97      | ~ l1_pre_topc(X1_52)
% 1.99/0.97      | ~ l1_pre_topc(X2_52)
% 1.99/0.97      | ~ v2_pre_topc(X1_52)
% 1.99/0.97      | ~ v2_pre_topc(X2_52)
% 1.99/0.97      | u1_struct_0(X3_52) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(X1_52) != u1_struct_0(sK0) ),
% 1.99/0.97      inference(subtyping,[status(esa)],[c_636]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_3003,plain,
% 1.99/0.97      ( ~ r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,sK3,X0_52,sK4),sK6)
% 1.99/0.97      | r1_tmap_1(sK3,X1_52,sK4,sK6)
% 1.99/0.97      | ~ v3_pre_topc(sK5,sK3)
% 1.99/0.97      | ~ m1_pre_topc(X0_52,sK3)
% 1.99/0.97      | ~ m1_pre_topc(sK3,X2_52)
% 1.99/0.97      | ~ r1_tarski(sK5,u1_struct_0(X0_52))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(X0_52))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_52))))
% 1.99/0.97      | v2_struct_0(X0_52)
% 1.99/0.97      | v2_struct_0(X1_52)
% 1.99/0.97      | v2_struct_0(X2_52)
% 1.99/0.97      | v2_struct_0(sK3)
% 1.99/0.97      | ~ l1_pre_topc(X1_52)
% 1.99/0.97      | ~ l1_pre_topc(X2_52)
% 1.99/0.97      | ~ v2_pre_topc(X1_52)
% 1.99/0.97      | ~ v2_pre_topc(X2_52)
% 1.99/0.97      | u1_struct_0(X1_52) != u1_struct_0(sK0)
% 1.99/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_1449]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_3377,plain,
% 1.99/0.97      ( r1_tmap_1(sK3,X0_52,sK4,sK6)
% 1.99/0.97      | ~ r1_tmap_1(sK2,X0_52,k3_tmap_1(X1_52,X0_52,sK3,sK2,sK4),sK6)
% 1.99/0.97      | ~ v3_pre_topc(sK5,sK3)
% 1.99/0.97      | ~ m1_pre_topc(sK3,X1_52)
% 1.99/0.97      | ~ m1_pre_topc(sK2,sK3)
% 1.99/0.97      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52))))
% 1.99/0.97      | v2_struct_0(X0_52)
% 1.99/0.97      | v2_struct_0(X1_52)
% 1.99/0.97      | v2_struct_0(sK3)
% 1.99/0.97      | v2_struct_0(sK2)
% 1.99/0.97      | ~ l1_pre_topc(X1_52)
% 1.99/0.97      | ~ l1_pre_topc(X0_52)
% 1.99/0.97      | ~ v2_pre_topc(X1_52)
% 1.99/0.97      | ~ v2_pre_topc(X0_52)
% 1.99/0.97      | u1_struct_0(X0_52) != u1_struct_0(sK0)
% 1.99/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_3003]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_3557,plain,
% 1.99/0.97      ( r1_tmap_1(sK3,X0_52,sK4,sK6)
% 1.99/0.97      | ~ r1_tmap_1(sK2,X0_52,k3_tmap_1(sK1,X0_52,sK3,sK2,sK4),sK6)
% 1.99/0.97      | ~ v3_pre_topc(sK5,sK3)
% 1.99/0.97      | ~ m1_pre_topc(sK3,sK1)
% 1.99/0.97      | ~ m1_pre_topc(sK2,sK3)
% 1.99/0.97      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52))))
% 1.99/0.97      | v2_struct_0(X0_52)
% 1.99/0.97      | v2_struct_0(sK3)
% 1.99/0.97      | v2_struct_0(sK1)
% 1.99/0.97      | v2_struct_0(sK2)
% 1.99/0.97      | ~ l1_pre_topc(X0_52)
% 1.99/0.97      | ~ l1_pre_topc(sK1)
% 1.99/0.97      | ~ v2_pre_topc(X0_52)
% 1.99/0.97      | ~ v2_pre_topc(sK1)
% 1.99/0.97      | u1_struct_0(X0_52) != u1_struct_0(sK0)
% 1.99/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_3377]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_3559,plain,
% 1.99/0.97      ( r1_tmap_1(sK3,sK0,sK4,sK6)
% 1.99/0.97      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 1.99/0.97      | ~ v3_pre_topc(sK5,sK3)
% 1.99/0.97      | ~ m1_pre_topc(sK3,sK1)
% 1.99/0.97      | ~ m1_pre_topc(sK2,sK3)
% 1.99/0.97      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.99/0.97      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 1.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
% 1.99/0.97      | v2_struct_0(sK3)
% 1.99/0.97      | v2_struct_0(sK1)
% 1.99/0.97      | v2_struct_0(sK0)
% 1.99/0.97      | v2_struct_0(sK2)
% 1.99/0.97      | ~ l1_pre_topc(sK1)
% 1.99/0.97      | ~ l1_pre_topc(sK0)
% 1.99/0.97      | ~ v2_pre_topc(sK1)
% 1.99/0.97      | ~ v2_pre_topc(sK0)
% 1.99/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.99/0.97      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_3557]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2516,plain,
% 1.99/0.97      ( r1_tmap_1(sK2,sK0,X0_53,X1_53)
% 1.99/0.97      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 1.99/0.97      | X0_53 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 1.99/0.97      | X1_53 != sK7 ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_1486]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2678,plain,
% 1.99/0.97      ( r1_tmap_1(sK2,sK0,X0_53,sK6)
% 1.99/0.97      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 1.99/0.97      | X0_53 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 1.99/0.97      | sK6 != sK7 ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_2516]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_3359,plain,
% 1.99/0.97      ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 1.99/0.97      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 1.99/0.97      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 1.99/0.97      | sK6 != sK7 ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_2678]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2919,plain,
% 1.99/0.97      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_1479]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1487,plain,
% 1.99/0.97      ( X0_53 != X1_53
% 1.99/0.97      | k3_tmap_1(X0_52,X1_52,X2_52,X3_52,X0_53) = k3_tmap_1(X0_52,X1_52,X2_52,X3_52,X1_53) ),
% 1.99/0.97      theory(equality) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2846,plain,
% 1.99/0.97      ( X0_53 != sK4
% 1.99/0.97      | k3_tmap_1(sK1,sK0,sK3,sK2,X0_53) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_1487]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2849,plain,
% 1.99/0.97      ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 1.99/0.97      | sK4 != sK4 ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_2846]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1473,plain,
% 1.99/0.97      ( ~ m1_pre_topc(X0_52,X1_52)
% 1.99/0.97      | ~ l1_pre_topc(X1_52)
% 1.99/0.97      | l1_pre_topc(X0_52) ),
% 1.99/0.97      inference(subtyping,[status(esa)],[c_3]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2710,plain,
% 1.99/0.97      ( ~ m1_pre_topc(sK3,X0_52)
% 1.99/0.97      | ~ l1_pre_topc(X0_52)
% 1.99/0.97      | l1_pre_topc(sK3) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_1473]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2839,plain,
% 1.99/0.97      ( ~ m1_pre_topc(sK3,sK1) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK1) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_2710]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1480,plain,
% 1.99/0.97      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 1.99/0.97      theory(equality) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2627,plain,
% 1.99/0.97      ( X0_53 != X1_53 | X0_53 = sK6 | sK6 != X1_53 ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_1480]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2765,plain,
% 1.99/0.97      ( X0_53 = sK6 | X0_53 != sK7 | sK6 != sK7 ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_2627]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2791,plain,
% 1.99/0.97      ( sK6 != sK7 | sK7 = sK6 | sK7 != sK7 ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_2765]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2657,plain,
% 1.99/0.97      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_1479]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1483,plain,
% 1.99/0.97      ( ~ m1_subset_1(X0_53,X0_54)
% 1.99/0.97      | m1_subset_1(X1_53,X1_54)
% 1.99/0.97      | X1_54 != X0_54
% 1.99/0.97      | X1_53 != X0_53 ),
% 1.99/0.97      theory(equality) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2486,plain,
% 1.99/0.97      ( m1_subset_1(X0_53,X0_54)
% 1.99/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK2))
% 1.99/0.97      | X0_54 != u1_struct_0(sK2)
% 1.99/0.97      | X0_53 != sK7 ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_1483]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2608,plain,
% 1.99/0.97      ( m1_subset_1(sK6,X0_54)
% 1.99/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK2))
% 1.99/0.97      | X0_54 != u1_struct_0(sK2)
% 1.99/0.97      | sK6 != sK7 ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_2486]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2656,plain,
% 1.99/0.97      ( m1_subset_1(sK6,u1_struct_0(sK2))
% 1.99/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK2))
% 1.99/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.99/0.97      | sK6 != sK7 ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_2608]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1478,plain,( X0_53 = X0_53 ),theory(equality) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2614,plain,
% 1.99/0.97      ( sK7 = sK7 ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_1478]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_4,plain,
% 1.99/0.97      ( ~ m1_pre_topc(X0,X1)
% 1.99/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.99/0.97      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/0.97      | ~ l1_pre_topc(X1) ),
% 1.99/0.97      inference(cnf_transformation,[],[f42]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1472,plain,
% 1.99/0.97      ( ~ m1_pre_topc(X0_52,X1_52)
% 1.99/0.97      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52)))
% 1.99/0.97      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X1_52)))
% 1.99/0.97      | ~ l1_pre_topc(X1_52) ),
% 1.99/0.97      inference(subtyping,[status(esa)],[c_4]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2456,plain,
% 1.99/0.97      ( ~ m1_pre_topc(sK2,sK3)
% 1.99/0.97      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.99/0.97      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.99/0.97      | ~ l1_pre_topc(sK3) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_1472]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2602,plain,
% 1.99/0.97      ( ~ m1_pre_topc(sK2,sK3)
% 1.99/0.97      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.99/0.97      | ~ l1_pre_topc(sK3) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_2456]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_5,plain,
% 1.99/0.97      ( ~ v3_pre_topc(X0,X1)
% 1.99/0.97      | v3_pre_topc(X0,X2)
% 1.99/0.97      | ~ m1_pre_topc(X2,X1)
% 1.99/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/0.97      | ~ l1_pre_topc(X1) ),
% 1.99/0.97      inference(cnf_transformation,[],[f71]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_1471,plain,
% 1.99/0.97      ( ~ v3_pre_topc(X0_53,X0_52)
% 1.99/0.97      | v3_pre_topc(X0_53,X1_52)
% 1.99/0.97      | ~ m1_pre_topc(X1_52,X0_52)
% 1.99/0.97      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X1_52)))
% 1.99/0.97      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52)))
% 1.99/0.97      | ~ l1_pre_topc(X0_52) ),
% 1.99/0.97      inference(subtyping,[status(esa)],[c_5]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2511,plain,
% 1.99/0.97      ( v3_pre_topc(sK5,X0_52)
% 1.99/0.97      | ~ v3_pre_topc(sK5,sK1)
% 1.99/0.97      | ~ m1_pre_topc(X0_52,sK1)
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_52)))
% 1.99/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/0.97      | ~ l1_pre_topc(sK1) ),
% 1.99/0.97      inference(instantiation,[status(thm)],[c_1471]) ).
% 1.99/0.97  
% 1.99/0.97  cnf(c_2601,plain,
% 1.99/0.97      ( v3_pre_topc(sK5,sK3)
% 1.99/0.98      | ~ v3_pre_topc(sK5,sK1)
% 1.99/0.98      | ~ m1_pre_topc(sK3,sK1)
% 1.99/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.99/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/0.98      | ~ l1_pre_topc(sK1) ),
% 1.99/0.98      inference(instantiation,[status(thm)],[c_2511]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_12,negated_conjecture,
% 1.99/0.98      ( sK6 = sK7 ),
% 1.99/0.98      inference(cnf_transformation,[],[f68]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_1467,negated_conjecture,
% 1.99/0.98      ( sK6 = sK7 ),
% 1.99/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_1497,plain,
% 1.99/0.98      ( sK4 = sK4 ),
% 1.99/0.98      inference(instantiation,[status(thm)],[c_1478]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_0,plain,
% 1.99/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.99/0.98      inference(cnf_transformation,[],[f39]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_209,plain,
% 1.99/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.99/0.98      inference(prop_impl,[status(thm)],[c_0]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_13,negated_conjecture,
% 1.99/0.98      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 1.99/0.98      inference(cnf_transformation,[],[f67]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_732,plain,
% 1.99/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.99/0.98      | u1_struct_0(sK2) != X1
% 1.99/0.98      | sK5 != X0 ),
% 1.99/0.98      inference(resolution_lifted,[status(thm)],[c_209,c_13]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_733,plain,
% 1.99/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.99/0.98      inference(unflattening,[status(thm)],[c_732]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_10,negated_conjecture,
% 1.99/0.98      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 1.99/0.98      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 1.99/0.98      inference(cnf_transformation,[],[f70]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_11,negated_conjecture,
% 1.99/0.98      ( r1_tmap_1(sK3,sK0,sK4,sK6)
% 1.99/0.98      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 1.99/0.98      inference(cnf_transformation,[],[f69]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_15,negated_conjecture,
% 1.99/0.98      ( v3_pre_topc(sK5,sK1) ),
% 1.99/0.98      inference(cnf_transformation,[],[f65]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_16,negated_conjecture,
% 1.99/0.98      ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
% 1.99/0.98      inference(cnf_transformation,[],[f64]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_17,negated_conjecture,
% 1.99/0.98      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.99/0.98      inference(cnf_transformation,[],[f63]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_18,negated_conjecture,
% 1.99/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.99/0.98      inference(cnf_transformation,[],[f62]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_19,negated_conjecture,
% 1.99/0.98      ( m1_pre_topc(sK2,sK3) ),
% 1.99/0.98      inference(cnf_transformation,[],[f61]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_20,negated_conjecture,
% 1.99/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
% 1.99/0.98      inference(cnf_transformation,[],[f60]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_23,negated_conjecture,
% 1.99/0.98      ( m1_pre_topc(sK3,sK1) ),
% 1.99/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_24,negated_conjecture,
% 1.99/0.98      ( ~ v2_struct_0(sK3) ),
% 1.99/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_26,negated_conjecture,
% 1.99/0.98      ( ~ v2_struct_0(sK2) ),
% 1.99/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_27,negated_conjecture,
% 1.99/0.98      ( l1_pre_topc(sK1) ),
% 1.99/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_28,negated_conjecture,
% 1.99/0.98      ( v2_pre_topc(sK1) ),
% 1.99/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_29,negated_conjecture,
% 1.99/0.98      ( ~ v2_struct_0(sK1) ),
% 1.99/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_30,negated_conjecture,
% 1.99/0.98      ( l1_pre_topc(sK0) ),
% 1.99/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_31,negated_conjecture,
% 1.99/0.98      ( v2_pre_topc(sK0) ),
% 1.99/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(c_32,negated_conjecture,
% 1.99/0.98      ( ~ v2_struct_0(sK0) ),
% 1.99/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.99/0.98  
% 1.99/0.98  cnf(contradiction,plain,
% 1.99/0.98      ( $false ),
% 1.99/0.98      inference(minisat,
% 1.99/0.98                [status(thm)],
% 1.99/0.98                [c_4469,c_3988,c_3924,c_3559,c_3359,c_2919,c_2849,c_2839,
% 1.99/0.98                 c_2791,c_2657,c_2656,c_2614,c_2602,c_2601,c_1467,c_1497,
% 1.99/0.98                 c_733,c_10,c_11,c_13,c_15,c_16,c_17,c_18,c_19,c_20,c_23,
% 1.99/0.98                 c_24,c_26,c_27,c_28,c_29,c_30,c_31,c_32]) ).
% 1.99/0.98  
% 1.99/0.98  
% 1.99/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.99/0.98  
% 1.99/0.98  ------                               Statistics
% 1.99/0.98  
% 1.99/0.98  ------ General
% 1.99/0.98  
% 1.99/0.98  abstr_ref_over_cycles:                  0
% 1.99/0.98  abstr_ref_under_cycles:                 0
% 1.99/0.98  gc_basic_clause_elim:                   0
% 1.99/0.98  forced_gc_time:                         0
% 1.99/0.98  parsing_time:                           0.009
% 1.99/0.98  unif_index_cands_time:                  0.
% 1.99/0.98  unif_index_add_time:                    0.
% 1.99/0.98  orderings_time:                         0.
% 1.99/0.98  out_proof_time:                         0.015
% 1.99/0.98  total_time:                             0.198
% 1.99/0.98  num_of_symbols:                         58
% 1.99/0.98  num_of_terms:                           2350
% 1.99/0.98  
% 1.99/0.98  ------ Preprocessing
% 1.99/0.98  
% 1.99/0.98  num_of_splits:                          0
% 1.99/0.98  num_of_split_atoms:                     0
% 1.99/0.98  num_of_reused_defs:                     0
% 1.99/0.98  num_eq_ax_congr_red:                    16
% 1.99/0.98  num_of_sem_filtered_clauses:            1
% 1.99/0.98  num_of_subtypes:                        3
% 1.99/0.98  monotx_restored_types:                  0
% 1.99/0.98  sat_num_of_epr_types:                   0
% 1.99/0.98  sat_num_of_non_cyclic_types:            0
% 1.99/0.98  sat_guarded_non_collapsed_types:        0
% 1.99/0.98  num_pure_diseq_elim:                    0
% 1.99/0.98  simp_replaced_by:                       0
% 1.99/0.98  res_preprocessed:                       143
% 1.99/0.98  prep_upred:                             0
% 1.99/0.98  prep_unflattend:                        22
% 1.99/0.98  smt_new_axioms:                         0
% 1.99/0.98  pred_elim_cands:                        8
% 1.99/0.98  pred_elim:                              4
% 1.99/0.98  pred_elim_cl:                           4
% 1.99/0.98  pred_elim_cycles:                       6
% 1.99/0.98  merged_defs:                            16
% 1.99/0.98  merged_defs_ncl:                        0
% 1.99/0.98  bin_hyper_res:                          16
% 1.99/0.98  prep_cycles:                            4
% 1.99/0.98  pred_elim_time:                         0.053
% 1.99/0.98  splitting_time:                         0.
% 1.99/0.98  sem_filter_time:                        0.
% 1.99/0.98  monotx_time:                            0.
% 1.99/0.98  subtype_inf_time:                       0.
% 1.99/0.98  
% 1.99/0.98  ------ Problem properties
% 1.99/0.98  
% 1.99/0.98  clauses:                                29
% 1.99/0.98  conjectures:                            20
% 1.99/0.98  epr:                                    16
% 1.99/0.98  horn:                                   26
% 1.99/0.98  ground:                                 20
% 1.99/0.98  unary:                                  18
% 1.99/0.98  binary:                                 4
% 1.99/0.98  lits:                                   88
% 1.99/0.98  lits_eq:                                5
% 1.99/0.98  fd_pure:                                0
% 1.99/0.98  fd_pseudo:                              0
% 1.99/0.98  fd_cond:                                0
% 1.99/0.98  fd_pseudo_cond:                         0
% 1.99/0.98  ac_symbols:                             0
% 1.99/0.98  
% 1.99/0.98  ------ Propositional Solver
% 1.99/0.98  
% 1.99/0.98  prop_solver_calls:                      29
% 1.99/0.98  prop_fast_solver_calls:                 1447
% 1.99/0.98  smt_solver_calls:                       0
% 1.99/0.98  smt_fast_solver_calls:                  0
% 1.99/0.98  prop_num_of_clauses:                    933
% 1.99/0.98  prop_preprocess_simplified:             3996
% 1.99/0.98  prop_fo_subsumed:                       33
% 1.99/0.98  prop_solver_time:                       0.
% 1.99/0.98  smt_solver_time:                        0.
% 1.99/0.98  smt_fast_solver_time:                   0.
% 1.99/0.98  prop_fast_solver_time:                  0.
% 1.99/0.98  prop_unsat_core_time:                   0.
% 1.99/0.98  
% 1.99/0.98  ------ QBF
% 1.99/0.98  
% 1.99/0.98  qbf_q_res:                              0
% 1.99/0.98  qbf_num_tautologies:                    0
% 1.99/0.98  qbf_prep_cycles:                        0
% 1.99/0.98  
% 1.99/0.98  ------ BMC1
% 1.99/0.98  
% 1.99/0.98  bmc1_current_bound:                     -1
% 1.99/0.98  bmc1_last_solved_bound:                 -1
% 1.99/0.98  bmc1_unsat_core_size:                   -1
% 1.99/0.98  bmc1_unsat_core_parents_size:           -1
% 1.99/0.98  bmc1_merge_next_fun:                    0
% 1.99/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.99/0.98  
% 1.99/0.98  ------ Instantiation
% 1.99/0.98  
% 1.99/0.98  inst_num_of_clauses:                    276
% 1.99/0.98  inst_num_in_passive:                    17
% 1.99/0.98  inst_num_in_active:                     252
% 1.99/0.98  inst_num_in_unprocessed:                6
% 1.99/0.98  inst_num_of_loops:                      292
% 1.99/0.98  inst_num_of_learning_restarts:          0
% 1.99/0.98  inst_num_moves_active_passive:          33
% 1.99/0.98  inst_lit_activity:                      0
% 1.99/0.98  inst_lit_activity_moves:                0
% 1.99/0.98  inst_num_tautologies:                   0
% 1.99/0.98  inst_num_prop_implied:                  0
% 1.99/0.98  inst_num_existing_simplified:           0
% 1.99/0.98  inst_num_eq_res_simplified:             0
% 1.99/0.98  inst_num_child_elim:                    0
% 1.99/0.98  inst_num_of_dismatching_blockings:      66
% 1.99/0.98  inst_num_of_non_proper_insts:           351
% 1.99/0.98  inst_num_of_duplicates:                 0
% 1.99/0.98  inst_inst_num_from_inst_to_res:         0
% 1.99/0.98  inst_dismatching_checking_time:         0.
% 1.99/0.98  
% 1.99/0.98  ------ Resolution
% 1.99/0.98  
% 1.99/0.98  res_num_of_clauses:                     0
% 1.99/0.98  res_num_in_passive:                     0
% 1.99/0.98  res_num_in_active:                      0
% 1.99/0.98  res_num_of_loops:                       147
% 1.99/0.98  res_forward_subset_subsumed:            89
% 1.99/0.98  res_backward_subset_subsumed:           0
% 1.99/0.98  res_forward_subsumed:                   0
% 1.99/0.98  res_backward_subsumed:                  0
% 1.99/0.98  res_forward_subsumption_resolution:     6
% 1.99/0.98  res_backward_subsumption_resolution:    0
% 1.99/0.98  res_clause_to_clause_subsumption:       291
% 1.99/0.98  res_orphan_elimination:                 0
% 1.99/0.98  res_tautology_del:                      123
% 1.99/0.98  res_num_eq_res_simplified:              0
% 1.99/0.98  res_num_sel_changes:                    0
% 1.99/0.98  res_moves_from_active_to_pass:          0
% 1.99/0.98  
% 1.99/0.98  ------ Superposition
% 1.99/0.98  
% 1.99/0.98  sup_time_total:                         0.
% 1.99/0.98  sup_time_generating:                    0.
% 1.99/0.98  sup_time_sim_full:                      0.
% 1.99/0.98  sup_time_sim_immed:                     0.
% 1.99/0.98  
% 1.99/0.98  sup_num_of_clauses:                     67
% 1.99/0.98  sup_num_in_active:                      58
% 1.99/0.98  sup_num_in_passive:                     9
% 1.99/0.98  sup_num_of_loops:                       58
% 1.99/0.98  sup_fw_superposition:                   39
% 1.99/0.98  sup_bw_superposition:                   17
% 1.99/0.98  sup_immediate_simplified:               8
% 1.99/0.98  sup_given_eliminated:                   0
% 1.99/0.98  comparisons_done:                       0
% 1.99/0.98  comparisons_avoided:                    0
% 1.99/0.98  
% 1.99/0.98  ------ Simplifications
% 1.99/0.98  
% 1.99/0.98  
% 1.99/0.98  sim_fw_subset_subsumed:                 8
% 1.99/0.98  sim_bw_subset_subsumed:                 0
% 1.99/0.98  sim_fw_subsumed:                        0
% 1.99/0.98  sim_bw_subsumed:                        0
% 1.99/0.98  sim_fw_subsumption_res:                 3
% 1.99/0.98  sim_bw_subsumption_res:                 0
% 1.99/0.98  sim_tautology_del:                      2
% 1.99/0.98  sim_eq_tautology_del:                   0
% 1.99/0.98  sim_eq_res_simp:                        0
% 1.99/0.98  sim_fw_demodulated:                     0
% 1.99/0.98  sim_bw_demodulated:                     0
% 1.99/0.98  sim_light_normalised:                   5
% 1.99/0.98  sim_joinable_taut:                      0
% 1.99/0.98  sim_joinable_simp:                      0
% 1.99/0.98  sim_ac_normalised:                      0
% 1.99/0.98  sim_smt_subsumption:                    0
% 1.99/0.98  
%------------------------------------------------------------------------------
