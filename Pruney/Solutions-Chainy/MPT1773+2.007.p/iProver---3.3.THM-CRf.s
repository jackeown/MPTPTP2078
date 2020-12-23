%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:09 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  221 (2382 expanded)
%              Number of clauses        :  156 ( 482 expanded)
%              Number of leaves         :   21 (1051 expanded)
%              Depth                    :   34
%              Number of atoms          : 1913 (50132 expanded)
%              Number of equality atoms :  559 (3501 expanded)
%              Maximal formula depth    :   31 (   9 average)
%              Maximal clause size      :   50 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
    inference(nnf_transformation,[],[f15])).

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
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f33,plain,(
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
     => ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7)
          | ~ r1_tmap_1(X3,X1,X4,X6) )
        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7)
          | r1_tmap_1(X3,X1,X4,X6) )
        & sK7 = X6
        & r1_tarski(X5,u1_struct_0(X2))
        & r2_hidden(X6,X5)
        & v3_pre_topc(X5,X3)
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
              | ~ r1_tmap_1(X3,X1,X4,sK6) )
            & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
              | r1_tmap_1(X3,X1,X4,sK6) )
            & sK6 = X7
            & r1_tarski(X5,u1_struct_0(X2))
            & r2_hidden(sK6,X5)
            & v3_pre_topc(X5,X3)
            & m1_subset_1(X7,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
                & r1_tarski(sK5,u1_struct_0(X2))
                & r2_hidden(X6,sK5)
                & v3_pre_topc(sK5,X3)
                & m1_subset_1(X7,u1_struct_0(X2)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
                    ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X7)
                      | ~ r1_tmap_1(X3,X1,sK4,X6) )
                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X7)
                      | r1_tmap_1(X3,X1,sK4,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(X2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,X3)
                    & m1_subset_1(X7,u1_struct_0(X2)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
                        ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X7)
                          | ~ r1_tmap_1(sK3,X1,X4,X6) )
                        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X7)
                          | r1_tmap_1(sK3,X1,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(X2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,sK3)
                        & m1_subset_1(X7,u1_struct_0(X2)) )
                    & m1_subset_1(X6,u1_struct_0(sK3)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) )
            & m1_pre_topc(X2,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
                            ( ( ~ r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X7)
                              | ~ r1_tmap_1(X3,X1,X4,X6) )
                            & ( r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X7)
                              | r1_tmap_1(X3,X1,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(sK2))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,X3)
                            & m1_subset_1(X7,u1_struct_0(sK2)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                & m1_pre_topc(sK2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
                                ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,sK1,X4,X6) )
                                & ( r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,sK1,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,X3)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
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
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7)
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
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
      | ~ r1_tmap_1(sK3,sK1,sK4,sK6) )
    & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
      | r1_tmap_1(sK3,sK1,sK4,sK6) )
    & sK6 = sK7
    & r1_tarski(sK5,u1_struct_0(sK2))
    & r2_hidden(sK6,sK5)
    & v3_pre_topc(sK5,sK3)
    & m1_subset_1(sK7,u1_struct_0(sK2))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f25,f33,f32,f31,f30,f29,f28,f27,f26])).

fof(f62,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
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
    inference(equality_resolution,[],[f42])).

fof(f63,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f48,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
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

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    v3_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
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
    inference(equality_resolution,[],[f43])).

fof(f66,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_4,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_420,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(X1,X0) != sK5
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_421,plain,
    ( m1_connsp_2(X0,X1,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK6,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(X1,X0) != sK5 ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_8,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_455,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X4) != u1_struct_0(sK2)
    | sK5 != X6 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_456,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(sK5,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X4) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_502,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(sK5,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X4) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_456,c_6])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_667,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_connsp_2(sK5,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X4) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_502,c_20])).

cnf(c_668,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_connsp_2(sK5,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_667])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_672,plain,
    ( ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_connsp_2(sK5,X3,X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_668,c_21])).

cnf(c_673,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_connsp_2(sK5,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_672])).

cnf(c_741,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X6)))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X6))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X6)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | X3 != X6
    | k1_tops_1(X6,X5) != sK5
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | sK5 != X5
    | sK6 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_421,c_673])).

cnf(c_742,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | ~ r1_tmap_1(X3,X1,sK4,sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k1_tops_1(X3,sK5) != sK5
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_741])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_790,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | ~ r1_tmap_1(X3,X1,sK4,sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k1_tops_1(X3,sK5) != sK5
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_742,c_0,c_1])).

cnf(c_1096,plain,
    ( r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),sK6)
    | ~ r1_tmap_1(X3_53,X1_53,sK4,sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_53)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK6,u1_struct_0(X3_53))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_pre_topc(X3_53,X2_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X3_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | u1_struct_0(X0_53) != u1_struct_0(sK2)
    | k1_tops_1(X3_53,sK5) != sK5 ),
    inference(subtyping,[status(esa)],[c_790])).

cnf(c_1698,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | u1_struct_0(X2_53) != u1_struct_0(sK2)
    | k1_tops_1(X0_53,sK5) != sK5
    | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4),sK6) = iProver_top
    | r1_tmap_1(X0_53,X1_53,sK4,sK6) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X2_53)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1096])).

cnf(c_11,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1113,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1781,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | u1_struct_0(X2_53) != u1_struct_0(sK2)
    | k1_tops_1(X0_53,sK5) != sK5
    | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4),sK7) = iProver_top
    | r1_tmap_1(X0_53,X1_53,sK4,sK7) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X2_53)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1698,c_1113])).

cnf(c_2308,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK2)
    | k1_tops_1(X0_53,sK5) != sK5
    | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),sK7) = iProver_top
    | r1_tmap_1(X0_53,sK1,sK4,sK7) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1781])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_36,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_37,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_46,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_47,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1122,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_2009,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1122])).

cnf(c_2030,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1122])).

cnf(c_1124,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_2022,plain,
    ( X0_54 != X1_54
    | X0_54 = sK6
    | sK6 != X1_54 ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_2178,plain,
    ( X0_54 = sK6
    | X0_54 != sK7
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2022])).

cnf(c_2232,plain,
    ( sK6 != sK7
    | sK7 = sK6
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2178])).

cnf(c_1127,plain,
    ( X0_55 != X1_55
    | k1_zfmisc_1(X0_55) = k1_zfmisc_1(X1_55) ),
    theory(equality)).

cnf(c_2148,plain,
    ( X0_55 != u1_struct_0(sK3)
    | k1_zfmisc_1(X0_55) = k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_2323,plain,
    ( k1_zfmisc_1(u1_struct_0(X0_53)) = k1_zfmisc_1(u1_struct_0(sK3))
    | u1_struct_0(X0_53) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2148])).

cnf(c_1128,plain,
    ( ~ m1_subset_1(X0_54,X0_55)
    | m1_subset_1(X1_54,X1_55)
    | X1_55 != X0_55
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_1979,plain,
    ( m1_subset_1(X0_54,X0_55)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | X0_55 != u1_struct_0(sK3)
    | X0_54 != sK6 ),
    inference(instantiation,[status(thm)],[c_1128])).

cnf(c_2520,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | m1_subset_1(sK7,X0_55)
    | X0_55 != u1_struct_0(sK3)
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_1979])).

cnf(c_2567,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | m1_subset_1(sK7,u1_struct_0(X0_53))
    | u1_struct_0(X0_53) != u1_struct_0(sK3)
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_2520])).

cnf(c_2568,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | sK7 != sK6
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2567])).

cnf(c_1984,plain,
    ( m1_subset_1(X0_54,X0_55)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0_55 != k1_zfmisc_1(u1_struct_0(sK3))
    | X0_54 != sK5 ),
    inference(instantiation,[status(thm)],[c_1128])).

cnf(c_2029,plain,
    ( m1_subset_1(sK5,X0_55)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0_55 != k1_zfmisc_1(u1_struct_0(sK3))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1984])).

cnf(c_2725,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | k1_zfmisc_1(u1_struct_0(X0_53)) != k1_zfmisc_1(u1_struct_0(sK3))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2029])).

cnf(c_2727,plain,
    ( k1_zfmisc_1(u1_struct_0(X0_53)) != k1_zfmisc_1(u1_struct_0(sK3))
    | sK5 != sK5
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2725])).

cnf(c_2814,plain,
    ( v2_pre_topc(X2_53) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
    | r1_tmap_1(X0_53,sK1,sK4,sK7) != iProver_top
    | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),sK7) = iProver_top
    | k1_tops_1(X0_53,sK5) != sK5
    | u1_struct_0(X1_53) != u1_struct_0(sK2)
    | u1_struct_0(X0_53) != u1_struct_0(sK3)
    | l1_pre_topc(X2_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2308,c_35,c_36,c_37,c_46,c_47,c_1113,c_2009,c_2030,c_2232,c_2323,c_2568,c_2727])).

cnf(c_2815,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK2)
    | k1_tops_1(X0_53,sK5) != sK5
    | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),sK7) = iProver_top
    | r1_tmap_1(X0_53,sK1,sK4,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2814])).

cnf(c_2834,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK2)
    | k1_tops_1(sK3,sK5) != sK5
    | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2815])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_14,negated_conjecture,
    ( v3_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK5 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_14])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(sK3,sK5) = sK5 ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_391,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(sK3,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_17])).

cnf(c_1097,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_53)
    | k1_tops_1(sK3,sK5) = sK5 ),
    inference(subtyping,[status(esa)],[c_391])).

cnf(c_1120,plain,
    ( ~ l1_pre_topc(sK3)
    | sP0_iProver_split
    | k1_tops_1(sK3,sK5) = sK5 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1097])).

cnf(c_1696,plain,
    ( k1_tops_1(sK3,sK5) = sK5
    | l1_pre_topc(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1120])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1117,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1949,plain,
    ( ~ m1_pre_topc(X0_53,sK0)
    | l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_1951,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1949])).

cnf(c_1118,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v2_pre_topc(X1_53)
    | v2_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1959,plain,
    ( ~ m1_pre_topc(X0_53,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1118])).

cnf(c_1961,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1959])).

cnf(c_1119,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X0_53)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1097])).

cnf(c_2234,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_1119])).

cnf(c_2757,plain,
    ( k1_tops_1(sK3,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1696,c_30,c_29,c_22,c_17,c_1120,c_1951,c_1961,c_2234])).

cnf(c_2835,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK2)
    | sK5 != sK5
    | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2834,c_2757])).

cnf(c_2836,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK2)
    | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2835])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_32,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_33,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_34,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_38,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_40,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_41,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_45,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_48,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1139,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1122])).

cnf(c_10,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1114,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1680,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1114])).

cnf(c_1745,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1680,c_1113])).

cnf(c_1123,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_2058,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1123])).

cnf(c_2091,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1123])).

cnf(c_1974,plain,
    ( m1_subset_1(X0_54,X0_55)
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | X0_55 != u1_struct_0(sK2)
    | X0_54 != sK7 ),
    inference(instantiation,[status(thm)],[c_1128])).

cnf(c_2003,plain,
    ( m1_subset_1(sK6,X0_55)
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | X0_55 != u1_struct_0(sK2)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_1974])).

cnf(c_2104,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2003])).

cnf(c_2106,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK6 != sK7
    | m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2104])).

cnf(c_2105,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1123])).

cnf(c_1129,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,X0_54,X1_54)
    | r1_tmap_1(X0_53,X1_53,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_1994,plain,
    ( r1_tmap_1(sK2,sK1,X0_54,X1_54)
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | X0_54 != k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | X1_54 != sK7 ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_2050,plain,
    ( r1_tmap_1(sK2,sK1,X0_54,sK6)
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | X0_54 != k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_1994])).

cnf(c_2110,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) != k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2050])).

cnf(c_2112,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) != k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | sK6 != sK7
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2110])).

cnf(c_2111,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1122])).

cnf(c_2254,plain,
    ( r1_tmap_1(sK3,sK1,X0_54,X1_54)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | X1_54 != sK6
    | X0_54 != sK4 ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_2529,plain,
    ( r1_tmap_1(sK3,sK1,X0_54,sK7)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | X0_54 != sK4
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_2254])).

cnf(c_2530,plain,
    ( X0_54 != sK4
    | sK7 != sK6
    | r1_tmap_1(sK3,sK1,X0_54,sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2529])).

cnf(c_2532,plain,
    ( sK7 != sK6
    | sK4 != sK4
    | r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2530])).

cnf(c_7,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_524,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X4) != u1_struct_0(sK2)
    | sK5 != X6 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_525,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(sK5,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X4) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_571,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(sK5,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X4) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_525,c_6])).

cnf(c_595,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_connsp_2(sK5,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X4) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_571,c_20])).

cnf(c_596,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_connsp_2(sK5,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_600,plain,
    ( ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_connsp_2(sK5,X3,X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_596,c_21])).

cnf(c_601,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_connsp_2(sK5,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_600])).

cnf(c_812,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X6)))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X6))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X6)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | X3 != X6
    | k1_tops_1(X6,X5) != sK5
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | sK5 != X5
    | sK6 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_421,c_601])).

cnf(c_813,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | r1_tmap_1(X3,X1,sK4,sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k1_tops_1(X3,sK5) != sK5
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_812])).

cnf(c_861,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | r1_tmap_1(X3,X1,sK4,sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k1_tops_1(X3,sK5) != sK5
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_813,c_0,c_1])).

cnf(c_1095,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),sK6)
    | r1_tmap_1(X3_53,X1_53,sK4,sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_53)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK6,u1_struct_0(X3_53))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_pre_topc(X3_53,X2_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X3_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | u1_struct_0(X0_53) != u1_struct_0(sK2)
    | k1_tops_1(X3_53,sK5) != sK5 ),
    inference(subtyping,[status(esa)],[c_861])).

cnf(c_2090,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,sK3,X0_53,sK4),sK6)
    | r1_tmap_1(sK3,X1_53,sK4,sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
    | ~ m1_pre_topc(X0_53,sK3)
    | ~ m1_pre_topc(sK3,X2_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | u1_struct_0(X0_53) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | k1_tops_1(sK3,sK5) != sK5 ),
    inference(instantiation,[status(thm)],[c_1095])).

cnf(c_2223,plain,
    ( r1_tmap_1(sK3,X0_53,sK4,sK6)
    | ~ r1_tmap_1(sK2,X0_53,k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4),sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
    | ~ m1_pre_topc(sK3,X1_53)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X0_53)
    | u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | k1_tops_1(sK3,sK5) != sK5 ),
    inference(instantiation,[status(thm)],[c_2090])).

cnf(c_2514,plain,
    ( r1_tmap_1(sK3,X0_53,sK4,sK6)
    | ~ r1_tmap_1(sK2,X0_53,k3_tmap_1(sK0,X0_53,sK3,sK2,sK4),sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK0)
    | u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | k1_tops_1(sK3,sK5) != sK5 ),
    inference(instantiation,[status(thm)],[c_2223])).

cnf(c_2558,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | k1_tops_1(sK3,sK5) != sK5 ),
    inference(instantiation,[status(thm)],[c_2514])).

cnf(c_2559,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | k1_tops_1(sK3,sK5) != sK5
    | r1_tmap_1(sK3,sK1,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2558])).

cnf(c_2893,plain,
    ( v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),sK7) = iProver_top
    | u1_struct_0(X0_53) != u1_struct_0(sK2)
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2836,c_32,c_30,c_33,c_29,c_34,c_35,c_36,c_37,c_38,c_40,c_22,c_41,c_44,c_45,c_17,c_46,c_47,c_48,c_1139,c_1113,c_1120,c_1745,c_1951,c_1961,c_2009,c_2058,c_2091,c_2106,c_2105,c_2112,c_2111,c_2232,c_2234,c_2532,c_2559])).

cnf(c_2894,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK2)
    | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2893])).

cnf(c_2908,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(X0_53,sK1,sK3,sK2,sK4),sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK3,X0_53) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2894])).

cnf(c_2992,plain,
    ( v2_struct_0(X0_53) = iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(X0_53,sK1,sK3,sK2,sK4),sK7) = iProver_top
    | m1_pre_topc(sK3,X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2908,c_38,c_45,c_48])).

cnf(c_2993,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(X0_53,sK1,sK3,sK2,sK4),sK7) = iProver_top
    | m1_pre_topc(sK3,X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2992])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1115,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1679,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1115])).

cnf(c_1750,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1679,c_1113])).

cnf(c_3003,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2993,c_1750])).

cnf(c_1699,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | u1_struct_0(X2_53) != u1_struct_0(sK2)
    | k1_tops_1(X0_53,sK5) != sK5
    | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4),sK6) != iProver_top
    | r1_tmap_1(X0_53,X1_53,sK4,sK6) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X2_53)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1095])).

cnf(c_1822,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | u1_struct_0(X2_53) != u1_struct_0(sK2)
    | k1_tops_1(X0_53,sK5) != sK5
    | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4),sK7) != iProver_top
    | r1_tmap_1(X0_53,X1_53,sK4,sK7) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X2_53)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1699,c_1113])).

cnf(c_2364,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK2)
    | k1_tops_1(X0_53,sK5) != sK5
    | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),sK7) != iProver_top
    | r1_tmap_1(X0_53,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1822])).

cnf(c_2841,plain,
    ( v2_pre_topc(X2_53) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
    | r1_tmap_1(X0_53,sK1,sK4,sK7) = iProver_top
    | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),sK7) != iProver_top
    | k1_tops_1(X0_53,sK5) != sK5
    | u1_struct_0(X1_53) != u1_struct_0(sK2)
    | u1_struct_0(X0_53) != u1_struct_0(sK3)
    | l1_pre_topc(X2_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2364,c_35,c_36,c_37,c_46,c_47,c_1113,c_2009,c_2030,c_2232,c_2323,c_2568,c_2727])).

cnf(c_2842,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK2)
    | k1_tops_1(X0_53,sK5) != sK5
    | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),sK7) != iProver_top
    | r1_tmap_1(X0_53,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2841])).

cnf(c_2861,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK2)
    | k1_tops_1(sK3,sK5) != sK5
    | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2842])).

cnf(c_2862,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK2)
    | sK5 != sK5
    | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2861,c_2757])).

cnf(c_2863,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK2)
    | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2862])).

cnf(c_2913,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2863,c_32,c_30,c_33,c_29,c_34,c_35,c_36,c_37,c_38,c_40,c_22,c_41,c_44,c_45,c_17,c_46,c_47,c_48,c_1139,c_1113,c_1120,c_1745,c_1951,c_1961,c_2009,c_2058,c_2091,c_2106,c_2105,c_2112,c_2111,c_2232,c_2234,c_2532,c_2559])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3003,c_2913,c_41,c_34,c_33,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:59:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.72/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/0.98  
% 1.72/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.72/0.98  
% 1.72/0.98  ------  iProver source info
% 1.72/0.98  
% 1.72/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.72/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.72/0.98  git: non_committed_changes: false
% 1.72/0.98  git: last_make_outside_of_git: false
% 1.72/0.98  
% 1.72/0.98  ------ 
% 1.72/0.98  
% 1.72/0.98  ------ Input Options
% 1.72/0.98  
% 1.72/0.98  --out_options                           all
% 1.72/0.98  --tptp_safe_out                         true
% 1.72/0.98  --problem_path                          ""
% 1.72/0.98  --include_path                          ""
% 1.72/0.98  --clausifier                            res/vclausify_rel
% 1.72/0.98  --clausifier_options                    --mode clausify
% 1.72/0.98  --stdin                                 false
% 1.72/0.98  --stats_out                             all
% 1.72/0.98  
% 1.72/0.98  ------ General Options
% 1.72/0.98  
% 1.72/0.98  --fof                                   false
% 1.72/0.98  --time_out_real                         305.
% 1.72/0.98  --time_out_virtual                      -1.
% 1.72/0.98  --symbol_type_check                     false
% 1.72/0.98  --clausify_out                          false
% 1.72/0.98  --sig_cnt_out                           false
% 1.72/0.98  --trig_cnt_out                          false
% 1.72/0.98  --trig_cnt_out_tolerance                1.
% 1.72/0.98  --trig_cnt_out_sk_spl                   false
% 1.72/0.98  --abstr_cl_out                          false
% 1.72/0.98  
% 1.72/0.98  ------ Global Options
% 1.72/0.98  
% 1.72/0.98  --schedule                              default
% 1.72/0.98  --add_important_lit                     false
% 1.72/0.98  --prop_solver_per_cl                    1000
% 1.72/0.98  --min_unsat_core                        false
% 1.72/0.98  --soft_assumptions                      false
% 1.72/0.98  --soft_lemma_size                       3
% 1.72/0.98  --prop_impl_unit_size                   0
% 1.72/0.98  --prop_impl_unit                        []
% 1.72/0.98  --share_sel_clauses                     true
% 1.72/0.98  --reset_solvers                         false
% 1.72/0.98  --bc_imp_inh                            [conj_cone]
% 1.72/0.98  --conj_cone_tolerance                   3.
% 1.72/0.98  --extra_neg_conj                        none
% 1.72/0.98  --large_theory_mode                     true
% 1.72/0.98  --prolific_symb_bound                   200
% 1.72/0.98  --lt_threshold                          2000
% 1.72/0.98  --clause_weak_htbl                      true
% 1.72/0.98  --gc_record_bc_elim                     false
% 1.72/0.98  
% 1.72/0.98  ------ Preprocessing Options
% 1.72/0.98  
% 1.72/0.98  --preprocessing_flag                    true
% 1.72/0.98  --time_out_prep_mult                    0.1
% 1.72/0.98  --splitting_mode                        input
% 1.72/0.98  --splitting_grd                         true
% 1.72/0.98  --splitting_cvd                         false
% 1.72/0.98  --splitting_cvd_svl                     false
% 1.72/0.98  --splitting_nvd                         32
% 1.72/0.98  --sub_typing                            true
% 1.72/0.98  --prep_gs_sim                           true
% 1.72/0.98  --prep_unflatten                        true
% 1.72/0.98  --prep_res_sim                          true
% 1.72/0.98  --prep_upred                            true
% 1.72/0.98  --prep_sem_filter                       exhaustive
% 1.72/0.98  --prep_sem_filter_out                   false
% 1.72/0.98  --pred_elim                             true
% 1.72/0.98  --res_sim_input                         true
% 1.72/0.98  --eq_ax_congr_red                       true
% 1.72/0.98  --pure_diseq_elim                       true
% 1.72/0.98  --brand_transform                       false
% 1.72/0.98  --non_eq_to_eq                          false
% 1.72/0.98  --prep_def_merge                        true
% 1.72/0.98  --prep_def_merge_prop_impl              false
% 1.72/0.98  --prep_def_merge_mbd                    true
% 1.72/0.98  --prep_def_merge_tr_red                 false
% 1.72/0.98  --prep_def_merge_tr_cl                  false
% 1.72/0.98  --smt_preprocessing                     true
% 1.72/0.98  --smt_ac_axioms                         fast
% 1.72/0.98  --preprocessed_out                      false
% 1.72/0.98  --preprocessed_stats                    false
% 1.72/0.98  
% 1.72/0.98  ------ Abstraction refinement Options
% 1.72/0.98  
% 1.72/0.98  --abstr_ref                             []
% 1.72/0.98  --abstr_ref_prep                        false
% 1.72/0.98  --abstr_ref_until_sat                   false
% 1.72/0.98  --abstr_ref_sig_restrict                funpre
% 1.72/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.72/0.98  --abstr_ref_under                       []
% 1.72/0.98  
% 1.72/0.98  ------ SAT Options
% 1.72/0.98  
% 1.72/0.98  --sat_mode                              false
% 1.72/0.98  --sat_fm_restart_options                ""
% 1.72/0.98  --sat_gr_def                            false
% 1.72/0.98  --sat_epr_types                         true
% 1.72/0.98  --sat_non_cyclic_types                  false
% 1.72/0.98  --sat_finite_models                     false
% 1.72/0.98  --sat_fm_lemmas                         false
% 1.72/0.98  --sat_fm_prep                           false
% 1.72/0.98  --sat_fm_uc_incr                        true
% 1.72/0.98  --sat_out_model                         small
% 1.72/0.98  --sat_out_clauses                       false
% 1.72/0.98  
% 1.72/0.98  ------ QBF Options
% 1.72/0.98  
% 1.72/0.98  --qbf_mode                              false
% 1.72/0.98  --qbf_elim_univ                         false
% 1.72/0.98  --qbf_dom_inst                          none
% 1.72/0.98  --qbf_dom_pre_inst                      false
% 1.72/0.98  --qbf_sk_in                             false
% 1.72/0.98  --qbf_pred_elim                         true
% 1.72/0.98  --qbf_split                             512
% 1.72/0.98  
% 1.72/0.98  ------ BMC1 Options
% 1.72/0.98  
% 1.72/0.98  --bmc1_incremental                      false
% 1.72/0.98  --bmc1_axioms                           reachable_all
% 1.72/0.98  --bmc1_min_bound                        0
% 1.72/0.98  --bmc1_max_bound                        -1
% 1.72/0.98  --bmc1_max_bound_default                -1
% 1.72/0.98  --bmc1_symbol_reachability              true
% 1.72/0.98  --bmc1_property_lemmas                  false
% 1.72/0.98  --bmc1_k_induction                      false
% 1.72/0.98  --bmc1_non_equiv_states                 false
% 1.72/0.98  --bmc1_deadlock                         false
% 1.72/0.98  --bmc1_ucm                              false
% 1.72/0.98  --bmc1_add_unsat_core                   none
% 1.72/0.98  --bmc1_unsat_core_children              false
% 1.72/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.72/0.98  --bmc1_out_stat                         full
% 1.72/0.98  --bmc1_ground_init                      false
% 1.72/0.98  --bmc1_pre_inst_next_state              false
% 1.72/0.98  --bmc1_pre_inst_state                   false
% 1.72/0.98  --bmc1_pre_inst_reach_state             false
% 1.72/0.98  --bmc1_out_unsat_core                   false
% 1.72/0.98  --bmc1_aig_witness_out                  false
% 1.72/0.98  --bmc1_verbose                          false
% 1.72/0.98  --bmc1_dump_clauses_tptp                false
% 1.72/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.72/0.98  --bmc1_dump_file                        -
% 1.72/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.72/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.72/0.98  --bmc1_ucm_extend_mode                  1
% 1.72/0.98  --bmc1_ucm_init_mode                    2
% 1.72/0.98  --bmc1_ucm_cone_mode                    none
% 1.72/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.72/0.98  --bmc1_ucm_relax_model                  4
% 1.72/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.72/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.72/0.98  --bmc1_ucm_layered_model                none
% 1.72/0.98  --bmc1_ucm_max_lemma_size               10
% 1.72/0.98  
% 1.72/0.98  ------ AIG Options
% 1.72/0.98  
% 1.72/0.98  --aig_mode                              false
% 1.72/0.98  
% 1.72/0.98  ------ Instantiation Options
% 1.72/0.98  
% 1.72/0.98  --instantiation_flag                    true
% 1.72/0.98  --inst_sos_flag                         false
% 1.72/0.98  --inst_sos_phase                        true
% 1.72/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.72/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.72/0.98  --inst_lit_sel_side                     num_symb
% 1.72/0.98  --inst_solver_per_active                1400
% 1.72/0.98  --inst_solver_calls_frac                1.
% 1.72/0.98  --inst_passive_queue_type               priority_queues
% 1.72/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.72/0.98  --inst_passive_queues_freq              [25;2]
% 1.72/0.98  --inst_dismatching                      true
% 1.72/0.98  --inst_eager_unprocessed_to_passive     true
% 1.72/0.98  --inst_prop_sim_given                   true
% 1.72/0.98  --inst_prop_sim_new                     false
% 1.72/0.98  --inst_subs_new                         false
% 1.72/0.99  --inst_eq_res_simp                      false
% 1.72/0.99  --inst_subs_given                       false
% 1.72/0.99  --inst_orphan_elimination               true
% 1.72/0.99  --inst_learning_loop_flag               true
% 1.72/0.99  --inst_learning_start                   3000
% 1.72/0.99  --inst_learning_factor                  2
% 1.72/0.99  --inst_start_prop_sim_after_learn       3
% 1.72/0.99  --inst_sel_renew                        solver
% 1.72/0.99  --inst_lit_activity_flag                true
% 1.72/0.99  --inst_restr_to_given                   false
% 1.72/0.99  --inst_activity_threshold               500
% 1.72/0.99  --inst_out_proof                        true
% 1.72/0.99  
% 1.72/0.99  ------ Resolution Options
% 1.72/0.99  
% 1.72/0.99  --resolution_flag                       true
% 1.72/0.99  --res_lit_sel                           adaptive
% 1.72/0.99  --res_lit_sel_side                      none
% 1.72/0.99  --res_ordering                          kbo
% 1.72/0.99  --res_to_prop_solver                    active
% 1.72/0.99  --res_prop_simpl_new                    false
% 1.72/0.99  --res_prop_simpl_given                  true
% 1.72/0.99  --res_passive_queue_type                priority_queues
% 1.72/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.72/0.99  --res_passive_queues_freq               [15;5]
% 1.72/0.99  --res_forward_subs                      full
% 1.72/0.99  --res_backward_subs                     full
% 1.72/0.99  --res_forward_subs_resolution           true
% 1.72/0.99  --res_backward_subs_resolution          true
% 1.72/0.99  --res_orphan_elimination                true
% 1.72/0.99  --res_time_limit                        2.
% 1.72/0.99  --res_out_proof                         true
% 1.72/0.99  
% 1.72/0.99  ------ Superposition Options
% 1.72/0.99  
% 1.72/0.99  --superposition_flag                    true
% 1.72/0.99  --sup_passive_queue_type                priority_queues
% 1.72/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.72/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.72/0.99  --demod_completeness_check              fast
% 1.72/0.99  --demod_use_ground                      true
% 1.72/0.99  --sup_to_prop_solver                    passive
% 1.72/0.99  --sup_prop_simpl_new                    true
% 1.72/0.99  --sup_prop_simpl_given                  true
% 1.72/0.99  --sup_fun_splitting                     false
% 1.72/0.99  --sup_smt_interval                      50000
% 1.72/0.99  
% 1.72/0.99  ------ Superposition Simplification Setup
% 1.72/0.99  
% 1.72/0.99  --sup_indices_passive                   []
% 1.72/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.72/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_full_bw                           [BwDemod]
% 1.72/0.99  --sup_immed_triv                        [TrivRules]
% 1.72/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.72/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_immed_bw_main                     []
% 1.72/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.72/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/0.99  
% 1.72/0.99  ------ Combination Options
% 1.72/0.99  
% 1.72/0.99  --comb_res_mult                         3
% 1.72/0.99  --comb_sup_mult                         2
% 1.72/0.99  --comb_inst_mult                        10
% 1.72/0.99  
% 1.72/0.99  ------ Debug Options
% 1.72/0.99  
% 1.72/0.99  --dbg_backtrace                         false
% 1.72/0.99  --dbg_dump_prop_clauses                 false
% 1.72/0.99  --dbg_dump_prop_clauses_file            -
% 1.72/0.99  --dbg_out_stat                          false
% 1.72/0.99  ------ Parsing...
% 1.72/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.72/0.99  
% 1.72/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.72/0.99  
% 1.72/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.72/0.99  
% 1.72/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.72/0.99  ------ Proving...
% 1.72/0.99  ------ Problem Properties 
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  clauses                                 25
% 1.72/0.99  conjectures                             18
% 1.72/0.99  EPR                                     15
% 1.72/0.99  Horn                                    21
% 1.72/0.99  unary                                   16
% 1.72/0.99  binary                                  2
% 1.72/0.99  lits                                    79
% 1.72/0.99  lits eq                                 10
% 1.72/0.99  fd_pure                                 0
% 1.72/0.99  fd_pseudo                               0
% 1.72/0.99  fd_cond                                 0
% 1.72/0.99  fd_pseudo_cond                          0
% 1.72/0.99  AC symbols                              0
% 1.72/0.99  
% 1.72/0.99  ------ Schedule dynamic 5 is on 
% 1.72/0.99  
% 1.72/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  ------ 
% 1.72/0.99  Current options:
% 1.72/0.99  ------ 
% 1.72/0.99  
% 1.72/0.99  ------ Input Options
% 1.72/0.99  
% 1.72/0.99  --out_options                           all
% 1.72/0.99  --tptp_safe_out                         true
% 1.72/0.99  --problem_path                          ""
% 1.72/0.99  --include_path                          ""
% 1.72/0.99  --clausifier                            res/vclausify_rel
% 1.72/0.99  --clausifier_options                    --mode clausify
% 1.72/0.99  --stdin                                 false
% 1.72/0.99  --stats_out                             all
% 1.72/0.99  
% 1.72/0.99  ------ General Options
% 1.72/0.99  
% 1.72/0.99  --fof                                   false
% 1.72/0.99  --time_out_real                         305.
% 1.72/0.99  --time_out_virtual                      -1.
% 1.72/0.99  --symbol_type_check                     false
% 1.72/0.99  --clausify_out                          false
% 1.72/0.99  --sig_cnt_out                           false
% 1.72/0.99  --trig_cnt_out                          false
% 1.72/0.99  --trig_cnt_out_tolerance                1.
% 1.72/0.99  --trig_cnt_out_sk_spl                   false
% 1.72/0.99  --abstr_cl_out                          false
% 1.72/0.99  
% 1.72/0.99  ------ Global Options
% 1.72/0.99  
% 1.72/0.99  --schedule                              default
% 1.72/0.99  --add_important_lit                     false
% 1.72/0.99  --prop_solver_per_cl                    1000
% 1.72/0.99  --min_unsat_core                        false
% 1.72/0.99  --soft_assumptions                      false
% 1.72/0.99  --soft_lemma_size                       3
% 1.72/0.99  --prop_impl_unit_size                   0
% 1.72/0.99  --prop_impl_unit                        []
% 1.72/0.99  --share_sel_clauses                     true
% 1.72/0.99  --reset_solvers                         false
% 1.72/0.99  --bc_imp_inh                            [conj_cone]
% 1.72/0.99  --conj_cone_tolerance                   3.
% 1.72/0.99  --extra_neg_conj                        none
% 1.72/0.99  --large_theory_mode                     true
% 1.72/0.99  --prolific_symb_bound                   200
% 1.72/0.99  --lt_threshold                          2000
% 1.72/0.99  --clause_weak_htbl                      true
% 1.72/0.99  --gc_record_bc_elim                     false
% 1.72/0.99  
% 1.72/0.99  ------ Preprocessing Options
% 1.72/0.99  
% 1.72/0.99  --preprocessing_flag                    true
% 1.72/0.99  --time_out_prep_mult                    0.1
% 1.72/0.99  --splitting_mode                        input
% 1.72/0.99  --splitting_grd                         true
% 1.72/0.99  --splitting_cvd                         false
% 1.72/0.99  --splitting_cvd_svl                     false
% 1.72/0.99  --splitting_nvd                         32
% 1.72/0.99  --sub_typing                            true
% 1.72/0.99  --prep_gs_sim                           true
% 1.72/0.99  --prep_unflatten                        true
% 1.72/0.99  --prep_res_sim                          true
% 1.72/0.99  --prep_upred                            true
% 1.72/0.99  --prep_sem_filter                       exhaustive
% 1.72/0.99  --prep_sem_filter_out                   false
% 1.72/0.99  --pred_elim                             true
% 1.72/0.99  --res_sim_input                         true
% 1.72/0.99  --eq_ax_congr_red                       true
% 1.72/0.99  --pure_diseq_elim                       true
% 1.72/0.99  --brand_transform                       false
% 1.72/0.99  --non_eq_to_eq                          false
% 1.72/0.99  --prep_def_merge                        true
% 1.72/0.99  --prep_def_merge_prop_impl              false
% 1.72/0.99  --prep_def_merge_mbd                    true
% 1.72/0.99  --prep_def_merge_tr_red                 false
% 1.72/0.99  --prep_def_merge_tr_cl                  false
% 1.72/0.99  --smt_preprocessing                     true
% 1.72/0.99  --smt_ac_axioms                         fast
% 1.72/0.99  --preprocessed_out                      false
% 1.72/0.99  --preprocessed_stats                    false
% 1.72/0.99  
% 1.72/0.99  ------ Abstraction refinement Options
% 1.72/0.99  
% 1.72/0.99  --abstr_ref                             []
% 1.72/0.99  --abstr_ref_prep                        false
% 1.72/0.99  --abstr_ref_until_sat                   false
% 1.72/0.99  --abstr_ref_sig_restrict                funpre
% 1.72/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.72/0.99  --abstr_ref_under                       []
% 1.72/0.99  
% 1.72/0.99  ------ SAT Options
% 1.72/0.99  
% 1.72/0.99  --sat_mode                              false
% 1.72/0.99  --sat_fm_restart_options                ""
% 1.72/0.99  --sat_gr_def                            false
% 1.72/0.99  --sat_epr_types                         true
% 1.72/0.99  --sat_non_cyclic_types                  false
% 1.72/0.99  --sat_finite_models                     false
% 1.72/0.99  --sat_fm_lemmas                         false
% 1.72/0.99  --sat_fm_prep                           false
% 1.72/0.99  --sat_fm_uc_incr                        true
% 1.72/0.99  --sat_out_model                         small
% 1.72/0.99  --sat_out_clauses                       false
% 1.72/0.99  
% 1.72/0.99  ------ QBF Options
% 1.72/0.99  
% 1.72/0.99  --qbf_mode                              false
% 1.72/0.99  --qbf_elim_univ                         false
% 1.72/0.99  --qbf_dom_inst                          none
% 1.72/0.99  --qbf_dom_pre_inst                      false
% 1.72/0.99  --qbf_sk_in                             false
% 1.72/0.99  --qbf_pred_elim                         true
% 1.72/0.99  --qbf_split                             512
% 1.72/0.99  
% 1.72/0.99  ------ BMC1 Options
% 1.72/0.99  
% 1.72/0.99  --bmc1_incremental                      false
% 1.72/0.99  --bmc1_axioms                           reachable_all
% 1.72/0.99  --bmc1_min_bound                        0
% 1.72/0.99  --bmc1_max_bound                        -1
% 1.72/0.99  --bmc1_max_bound_default                -1
% 1.72/0.99  --bmc1_symbol_reachability              true
% 1.72/0.99  --bmc1_property_lemmas                  false
% 1.72/0.99  --bmc1_k_induction                      false
% 1.72/0.99  --bmc1_non_equiv_states                 false
% 1.72/0.99  --bmc1_deadlock                         false
% 1.72/0.99  --bmc1_ucm                              false
% 1.72/0.99  --bmc1_add_unsat_core                   none
% 1.72/0.99  --bmc1_unsat_core_children              false
% 1.72/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.72/0.99  --bmc1_out_stat                         full
% 1.72/0.99  --bmc1_ground_init                      false
% 1.72/0.99  --bmc1_pre_inst_next_state              false
% 1.72/0.99  --bmc1_pre_inst_state                   false
% 1.72/0.99  --bmc1_pre_inst_reach_state             false
% 1.72/0.99  --bmc1_out_unsat_core                   false
% 1.72/0.99  --bmc1_aig_witness_out                  false
% 1.72/0.99  --bmc1_verbose                          false
% 1.72/0.99  --bmc1_dump_clauses_tptp                false
% 1.72/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.72/0.99  --bmc1_dump_file                        -
% 1.72/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.72/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.72/0.99  --bmc1_ucm_extend_mode                  1
% 1.72/0.99  --bmc1_ucm_init_mode                    2
% 1.72/0.99  --bmc1_ucm_cone_mode                    none
% 1.72/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.72/0.99  --bmc1_ucm_relax_model                  4
% 1.72/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.72/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.72/0.99  --bmc1_ucm_layered_model                none
% 1.72/0.99  --bmc1_ucm_max_lemma_size               10
% 1.72/0.99  
% 1.72/0.99  ------ AIG Options
% 1.72/0.99  
% 1.72/0.99  --aig_mode                              false
% 1.72/0.99  
% 1.72/0.99  ------ Instantiation Options
% 1.72/0.99  
% 1.72/0.99  --instantiation_flag                    true
% 1.72/0.99  --inst_sos_flag                         false
% 1.72/0.99  --inst_sos_phase                        true
% 1.72/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.72/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.72/0.99  --inst_lit_sel_side                     none
% 1.72/0.99  --inst_solver_per_active                1400
% 1.72/0.99  --inst_solver_calls_frac                1.
% 1.72/0.99  --inst_passive_queue_type               priority_queues
% 1.72/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.72/0.99  --inst_passive_queues_freq              [25;2]
% 1.72/0.99  --inst_dismatching                      true
% 1.72/0.99  --inst_eager_unprocessed_to_passive     true
% 1.72/0.99  --inst_prop_sim_given                   true
% 1.72/0.99  --inst_prop_sim_new                     false
% 1.72/0.99  --inst_subs_new                         false
% 1.72/0.99  --inst_eq_res_simp                      false
% 1.72/0.99  --inst_subs_given                       false
% 1.72/0.99  --inst_orphan_elimination               true
% 1.72/0.99  --inst_learning_loop_flag               true
% 1.72/0.99  --inst_learning_start                   3000
% 1.72/0.99  --inst_learning_factor                  2
% 1.72/0.99  --inst_start_prop_sim_after_learn       3
% 1.72/0.99  --inst_sel_renew                        solver
% 1.72/0.99  --inst_lit_activity_flag                true
% 1.72/0.99  --inst_restr_to_given                   false
% 1.72/0.99  --inst_activity_threshold               500
% 1.72/0.99  --inst_out_proof                        true
% 1.72/0.99  
% 1.72/0.99  ------ Resolution Options
% 1.72/0.99  
% 1.72/0.99  --resolution_flag                       false
% 1.72/0.99  --res_lit_sel                           adaptive
% 1.72/0.99  --res_lit_sel_side                      none
% 1.72/0.99  --res_ordering                          kbo
% 1.72/0.99  --res_to_prop_solver                    active
% 1.72/0.99  --res_prop_simpl_new                    false
% 1.72/0.99  --res_prop_simpl_given                  true
% 1.72/0.99  --res_passive_queue_type                priority_queues
% 1.72/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.72/0.99  --res_passive_queues_freq               [15;5]
% 1.72/0.99  --res_forward_subs                      full
% 1.72/0.99  --res_backward_subs                     full
% 1.72/0.99  --res_forward_subs_resolution           true
% 1.72/0.99  --res_backward_subs_resolution          true
% 1.72/0.99  --res_orphan_elimination                true
% 1.72/0.99  --res_time_limit                        2.
% 1.72/0.99  --res_out_proof                         true
% 1.72/0.99  
% 1.72/0.99  ------ Superposition Options
% 1.72/0.99  
% 1.72/0.99  --superposition_flag                    true
% 1.72/0.99  --sup_passive_queue_type                priority_queues
% 1.72/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.72/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.72/0.99  --demod_completeness_check              fast
% 1.72/0.99  --demod_use_ground                      true
% 1.72/0.99  --sup_to_prop_solver                    passive
% 1.72/0.99  --sup_prop_simpl_new                    true
% 1.72/0.99  --sup_prop_simpl_given                  true
% 1.72/0.99  --sup_fun_splitting                     false
% 1.72/0.99  --sup_smt_interval                      50000
% 1.72/0.99  
% 1.72/0.99  ------ Superposition Simplification Setup
% 1.72/0.99  
% 1.72/0.99  --sup_indices_passive                   []
% 1.72/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.72/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_full_bw                           [BwDemod]
% 1.72/0.99  --sup_immed_triv                        [TrivRules]
% 1.72/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.72/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_immed_bw_main                     []
% 1.72/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.72/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/0.99  
% 1.72/0.99  ------ Combination Options
% 1.72/0.99  
% 1.72/0.99  --comb_res_mult                         3
% 1.72/0.99  --comb_sup_mult                         2
% 1.72/0.99  --comb_inst_mult                        10
% 1.72/0.99  
% 1.72/0.99  ------ Debug Options
% 1.72/0.99  
% 1.72/0.99  --dbg_backtrace                         false
% 1.72/0.99  --dbg_dump_prop_clauses                 false
% 1.72/0.99  --dbg_dump_prop_clauses_file            -
% 1.72/0.99  --dbg_out_stat                          false
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  ------ Proving...
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  % SZS status Theorem for theBenchmark.p
% 1.72/0.99  
% 1.72/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.72/0.99  
% 1.72/0.99  fof(f4,axiom,(
% 1.72/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f14,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.72/0.99    inference(ennf_transformation,[],[f4])).
% 1.72/0.99  
% 1.72/0.99  fof(f15,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/0.99    inference(flattening,[],[f14])).
% 1.72/0.99  
% 1.72/0.99  fof(f22,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/0.99    inference(nnf_transformation,[],[f15])).
% 1.72/0.99  
% 1.72/0.99  fof(f40,plain,(
% 1.72/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f22])).
% 1.72/0.99  
% 1.72/0.99  fof(f7,conjecture,(
% 1.72/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f8,negated_conjecture,(
% 1.72/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.72/0.99    inference(negated_conjecture,[],[f7])).
% 1.72/0.99  
% 1.72/0.99  fof(f20,plain,(
% 1.72/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.72/0.99    inference(ennf_transformation,[],[f8])).
% 1.72/0.99  
% 1.72/0.99  fof(f21,plain,(
% 1.72/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.72/0.99    inference(flattening,[],[f20])).
% 1.72/0.99  
% 1.72/0.99  fof(f24,plain,(
% 1.72/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.72/0.99    inference(nnf_transformation,[],[f21])).
% 1.72/0.99  
% 1.72/0.99  fof(f25,plain,(
% 1.72/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.72/0.99    inference(flattening,[],[f24])).
% 1.72/0.99  
% 1.72/0.99  fof(f33,plain,(
% 1.72/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) | r1_tmap_1(X3,X1,X4,X6)) & sK7 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 1.72/0.99    introduced(choice_axiom,[])).
% 1.72/0.99  
% 1.72/0.99  fof(f32,plain,(
% 1.72/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,sK6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,sK6)) & sK6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 1.72/0.99    introduced(choice_axiom,[])).
% 1.72/0.99  
% 1.72/0.99  fof(f31,plain,(
% 1.72/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(X2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))))) )),
% 1.72/0.99    introduced(choice_axiom,[])).
% 1.72/0.99  
% 1.72/0.99  fof(f30,plain,(
% 1.72/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X7) | ~r1_tmap_1(X3,X1,sK4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X7) | r1_tmap_1(X3,X1,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 1.72/0.99    introduced(choice_axiom,[])).
% 1.72/0.99  
% 1.72/0.99  fof(f29,plain,(
% 1.72/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X7) | ~r1_tmap_1(sK3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X7) | r1_tmap_1(sK3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 1.72/0.99    introduced(choice_axiom,[])).
% 1.72/0.99  
% 1.72/0.99  fof(f28,plain,(
% 1.72/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 1.72/0.99    introduced(choice_axiom,[])).
% 1.72/0.99  
% 1.72/0.99  fof(f27,plain,(
% 1.72/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.72/0.99    introduced(choice_axiom,[])).
% 1.72/0.99  
% 1.72/0.99  fof(f26,plain,(
% 1.72/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.72/0.99    introduced(choice_axiom,[])).
% 1.72/0.99  
% 1.72/0.99  fof(f34,plain,(
% 1.72/0.99    ((((((((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK3) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f25,f33,f32,f31,f30,f29,f28,f27,f26])).
% 1.72/0.99  
% 1.72/0.99  fof(f62,plain,(
% 1.72/0.99    r2_hidden(sK6,sK5)),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f6,axiom,(
% 1.72/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f18,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.72/0.99    inference(ennf_transformation,[],[f6])).
% 1.72/0.99  
% 1.72/0.99  fof(f19,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/0.99    inference(flattening,[],[f18])).
% 1.72/0.99  
% 1.72/0.99  fof(f23,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/0.99    inference(nnf_transformation,[],[f19])).
% 1.72/0.99  
% 1.72/0.99  fof(f42,plain,(
% 1.72/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f23])).
% 1.72/0.99  
% 1.72/0.99  fof(f68,plain,(
% 1.72/0.99    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/0.99    inference(equality_resolution,[],[f42])).
% 1.72/0.99  
% 1.72/0.99  fof(f63,plain,(
% 1.72/0.99    r1_tarski(sK5,u1_struct_0(sK2))),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f5,axiom,(
% 1.72/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f16,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.72/0.99    inference(ennf_transformation,[],[f5])).
% 1.72/0.99  
% 1.72/0.99  fof(f17,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.72/0.99    inference(flattening,[],[f16])).
% 1.72/0.99  
% 1.72/0.99  fof(f41,plain,(
% 1.72/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f17])).
% 1.72/0.99  
% 1.72/0.99  fof(f55,plain,(
% 1.72/0.99    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f54,plain,(
% 1.72/0.99    v1_funct_1(sK4)),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f1,axiom,(
% 1.72/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f9,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.72/0.99    inference(ennf_transformation,[],[f1])).
% 1.72/0.99  
% 1.72/0.99  fof(f10,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.72/0.99    inference(flattening,[],[f9])).
% 1.72/0.99  
% 1.72/0.99  fof(f35,plain,(
% 1.72/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f10])).
% 1.72/0.99  
% 1.72/0.99  fof(f2,axiom,(
% 1.72/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f11,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.72/0.99    inference(ennf_transformation,[],[f2])).
% 1.72/0.99  
% 1.72/0.99  fof(f36,plain,(
% 1.72/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f11])).
% 1.72/0.99  
% 1.72/0.99  fof(f64,plain,(
% 1.72/0.99    sK6 = sK7),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f47,plain,(
% 1.72/0.99    ~v2_struct_0(sK1)),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f48,plain,(
% 1.72/0.99    v2_pre_topc(sK1)),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f49,plain,(
% 1.72/0.99    l1_pre_topc(sK1)),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f58,plain,(
% 1.72/0.99    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f59,plain,(
% 1.72/0.99    m1_subset_1(sK6,u1_struct_0(sK3))),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f3,axiom,(
% 1.72/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f12,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.72/0.99    inference(ennf_transformation,[],[f3])).
% 1.72/0.99  
% 1.72/0.99  fof(f13,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.72/0.99    inference(flattening,[],[f12])).
% 1.72/0.99  
% 1.72/0.99  fof(f37,plain,(
% 1.72/0.99    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f13])).
% 1.72/0.99  
% 1.72/0.99  fof(f61,plain,(
% 1.72/0.99    v3_pre_topc(sK5,sK3)),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f45,plain,(
% 1.72/0.99    v2_pre_topc(sK0)),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f46,plain,(
% 1.72/0.99    l1_pre_topc(sK0)),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f53,plain,(
% 1.72/0.99    m1_pre_topc(sK3,sK0)),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f44,plain,(
% 1.72/0.99    ~v2_struct_0(sK0)),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f50,plain,(
% 1.72/0.99    ~v2_struct_0(sK2)),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f52,plain,(
% 1.72/0.99    ~v2_struct_0(sK3)),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f56,plain,(
% 1.72/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f57,plain,(
% 1.72/0.99    m1_pre_topc(sK2,sK3)),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f60,plain,(
% 1.72/0.99    m1_subset_1(sK7,u1_struct_0(sK2))),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f65,plain,(
% 1.72/0.99    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  fof(f43,plain,(
% 1.72/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f23])).
% 1.72/0.99  
% 1.72/0.99  fof(f67,plain,(
% 1.72/0.99    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/0.99    inference(equality_resolution,[],[f43])).
% 1.72/0.99  
% 1.72/0.99  fof(f66,plain,(
% 1.72/0.99    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)),
% 1.72/0.99    inference(cnf_transformation,[],[f34])).
% 1.72/0.99  
% 1.72/0.99  cnf(c_4,plain,
% 1.72/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.72/0.99      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.72/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X1) ),
% 1.72/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_13,negated_conjecture,
% 1.72/0.99      ( r2_hidden(sK6,sK5) ),
% 1.72/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_420,plain,
% 1.72/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.72/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | k1_tops_1(X1,X0) != sK5
% 1.72/0.99      | sK6 != X2 ),
% 1.72/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_421,plain,
% 1.72/0.99      ( m1_connsp_2(X0,X1,sK6)
% 1.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X1))
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | k1_tops_1(X1,X0) != sK5 ),
% 1.72/0.99      inference(unflattening,[status(thm)],[c_420]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_8,plain,
% 1.72/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.72/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.72/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.72/0.99      | ~ m1_connsp_2(X6,X0,X3)
% 1.72/0.99      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_pre_topc(X4,X0)
% 1.72/0.99      | ~ m1_pre_topc(X0,X5)
% 1.72/0.99      | ~ m1_pre_topc(X4,X5)
% 1.72/0.99      | ~ v1_funct_1(X2)
% 1.72/0.99      | v2_struct_0(X5)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X4)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | ~ l1_pre_topc(X5)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X5)
% 1.72/0.99      | ~ v2_pre_topc(X1) ),
% 1.72/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_12,negated_conjecture,
% 1.72/0.99      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 1.72/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_455,plain,
% 1.72/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.72/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.72/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.72/0.99      | ~ m1_connsp_2(X6,X0,X3)
% 1.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_pre_topc(X4,X0)
% 1.72/0.99      | ~ m1_pre_topc(X0,X5)
% 1.72/0.99      | ~ m1_pre_topc(X4,X5)
% 1.72/0.99      | ~ v1_funct_1(X2)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X5)
% 1.72/0.99      | v2_struct_0(X4)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X5)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X5)
% 1.72/0.99      | u1_struct_0(X4) != u1_struct_0(sK2)
% 1.72/0.99      | sK5 != X6 ),
% 1.72/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_456,plain,
% 1.72/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.72/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.72/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.72/0.99      | ~ m1_connsp_2(sK5,X0,X3)
% 1.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.72/0.99      | ~ m1_pre_topc(X4,X0)
% 1.72/0.99      | ~ m1_pre_topc(X0,X5)
% 1.72/0.99      | ~ m1_pre_topc(X4,X5)
% 1.72/0.99      | ~ v1_funct_1(X2)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X5)
% 1.72/0.99      | v2_struct_0(X4)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X5)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X5)
% 1.72/0.99      | u1_struct_0(X4) != u1_struct_0(sK2) ),
% 1.72/0.99      inference(unflattening,[status(thm)],[c_455]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_6,plain,
% 1.72/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.72/0.99      | ~ m1_pre_topc(X2,X0)
% 1.72/0.99      | m1_pre_topc(X2,X1)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X1) ),
% 1.72/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_502,plain,
% 1.72/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.72/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.72/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.72/0.99      | ~ m1_connsp_2(sK5,X0,X3)
% 1.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.72/0.99      | ~ m1_pre_topc(X4,X0)
% 1.72/0.99      | ~ m1_pre_topc(X0,X5)
% 1.72/0.99      | ~ v1_funct_1(X2)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X5)
% 1.72/0.99      | v2_struct_0(X4)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X5)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X5)
% 1.72/0.99      | u1_struct_0(X4) != u1_struct_0(sK2) ),
% 1.72/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_456,c_6]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_20,negated_conjecture,
% 1.72/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 1.72/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_667,plain,
% 1.72/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.72/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.72/0.99      | ~ m1_connsp_2(sK5,X0,X3)
% 1.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.72/0.99      | ~ m1_pre_topc(X4,X0)
% 1.72/0.99      | ~ m1_pre_topc(X0,X5)
% 1.72/0.99      | ~ v1_funct_1(X2)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X5)
% 1.72/0.99      | v2_struct_0(X4)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X5)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X5)
% 1.72/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X4) != u1_struct_0(sK2)
% 1.72/0.99      | sK4 != X2 ),
% 1.72/0.99      inference(resolution_lifted,[status(thm)],[c_502,c_20]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_668,plain,
% 1.72/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.72/0.99      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.72/0.99      | ~ m1_connsp_2(sK5,X3,X4)
% 1.72/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_pre_topc(X0,X3)
% 1.72/0.99      | ~ m1_pre_topc(X3,X2)
% 1.72/0.99      | ~ v1_funct_1(sK4)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X3)
% 1.72/0.99      | v2_struct_0(X2)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X2)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X2)
% 1.72/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.72/0.99      inference(unflattening,[status(thm)],[c_667]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_21,negated_conjecture,
% 1.72/0.99      ( v1_funct_1(sK4) ),
% 1.72/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_672,plain,
% 1.72/0.99      ( ~ m1_pre_topc(X3,X2)
% 1.72/0.99      | ~ m1_pre_topc(X0,X3)
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.72/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.72/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_connsp_2(sK5,X3,X4)
% 1.72/0.99      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.72/0.99      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X3)
% 1.72/0.99      | v2_struct_0(X2)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X2)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X2)
% 1.72/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.72/0.99      inference(global_propositional_subsumption,
% 1.72/0.99                [status(thm)],
% 1.72/0.99                [c_668,c_21]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_673,plain,
% 1.72/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.72/0.99      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.72/0.99      | ~ m1_connsp_2(sK5,X3,X4)
% 1.72/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_pre_topc(X0,X3)
% 1.72/0.99      | ~ m1_pre_topc(X3,X2)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X2)
% 1.72/0.99      | v2_struct_0(X3)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X2)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X2)
% 1.72/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.72/0.99      inference(renaming,[status(thm)],[c_672]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_741,plain,
% 1.72/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.72/0.99      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.72/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X6)))
% 1.72/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X6))
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_pre_topc(X0,X3)
% 1.72/0.99      | ~ m1_pre_topc(X3,X2)
% 1.72/0.99      | v2_struct_0(X6)
% 1.72/0.99      | v2_struct_0(X3)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X2)
% 1.72/0.99      | ~ l1_pre_topc(X6)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X2)
% 1.72/0.99      | ~ v2_pre_topc(X6)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X2)
% 1.72/0.99      | X3 != X6
% 1.72/0.99      | k1_tops_1(X6,X5) != sK5
% 1.72/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.72/0.99      | sK5 != X5
% 1.72/0.99      | sK6 != X4 ),
% 1.72/0.99      inference(resolution_lifted,[status(thm)],[c_421,c_673]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_742,plain,
% 1.72/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 1.72/0.99      | ~ r1_tmap_1(X3,X1,sK4,sK6)
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_pre_topc(X0,X3)
% 1.72/0.99      | ~ m1_pre_topc(X3,X2)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X2)
% 1.72/0.99      | v2_struct_0(X3)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X2)
% 1.72/0.99      | ~ l1_pre_topc(X3)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X2)
% 1.72/0.99      | ~ v2_pre_topc(X3)
% 1.72/0.99      | k1_tops_1(X3,sK5) != sK5
% 1.72/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.72/0.99      inference(unflattening,[status(thm)],[c_741]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_0,plain,
% 1.72/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | v2_pre_topc(X0) ),
% 1.72/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1,plain,
% 1.72/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.72/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_790,plain,
% 1.72/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 1.72/0.99      | ~ r1_tmap_1(X3,X1,sK4,sK6)
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_pre_topc(X0,X3)
% 1.72/0.99      | ~ m1_pre_topc(X3,X2)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X2)
% 1.72/0.99      | v2_struct_0(X3)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X2)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X2)
% 1.72/0.99      | k1_tops_1(X3,sK5) != sK5
% 1.72/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.72/0.99      inference(forward_subsumption_resolution,
% 1.72/0.99                [status(thm)],
% 1.72/0.99                [c_742,c_0,c_1]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1096,plain,
% 1.72/0.99      ( r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),sK6)
% 1.72/0.99      | ~ r1_tmap_1(X3_53,X1_53,sK4,sK6)
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_53)))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3_53))
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
% 1.72/0.99      | ~ m1_pre_topc(X0_53,X3_53)
% 1.72/0.99      | ~ m1_pre_topc(X3_53,X2_53)
% 1.72/0.99      | v2_struct_0(X1_53)
% 1.72/0.99      | v2_struct_0(X0_53)
% 1.72/0.99      | v2_struct_0(X2_53)
% 1.72/0.99      | v2_struct_0(X3_53)
% 1.72/0.99      | ~ l1_pre_topc(X1_53)
% 1.72/0.99      | ~ l1_pre_topc(X2_53)
% 1.72/0.99      | ~ v2_pre_topc(X1_53)
% 1.72/0.99      | ~ v2_pre_topc(X2_53)
% 1.72/0.99      | u1_struct_0(X3_53) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X0_53) != u1_struct_0(sK2)
% 1.72/0.99      | k1_tops_1(X3_53,sK5) != sK5 ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_790]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1698,plain,
% 1.72/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X2_53) != u1_struct_0(sK2)
% 1.72/0.99      | k1_tops_1(X0_53,sK5) != sK5
% 1.72/0.99      | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4),sK6) = iProver_top
% 1.72/0.99      | r1_tmap_1(X0_53,X1_53,sK4,sK6) != iProver_top
% 1.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 1.72/0.99      | m1_subset_1(sK6,u1_struct_0(X2_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK6,u1_struct_0(X0_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 1.72/0.99      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X2_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X3_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | l1_pre_topc(X1_53) != iProver_top
% 1.72/0.99      | l1_pre_topc(X3_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X1_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X3_53) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1096]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_11,negated_conjecture,
% 1.72/0.99      ( sK6 = sK7 ),
% 1.72/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1113,negated_conjecture,
% 1.72/0.99      ( sK6 = sK7 ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1781,plain,
% 1.72/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X2_53) != u1_struct_0(sK2)
% 1.72/0.99      | k1_tops_1(X0_53,sK5) != sK5
% 1.72/0.99      | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4),sK7) = iProver_top
% 1.72/0.99      | r1_tmap_1(X0_53,X1_53,sK4,sK7) != iProver_top
% 1.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X2_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 1.72/0.99      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X2_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X3_53) = iProver_top
% 1.72/0.99      | l1_pre_topc(X1_53) != iProver_top
% 1.72/0.99      | l1_pre_topc(X3_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X1_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X3_53) != iProver_top ),
% 1.72/0.99      inference(light_normalisation,[status(thm)],[c_1698,c_1113]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2308,plain,
% 1.72/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK2)
% 1.72/0.99      | k1_tops_1(X0_53,sK5) != sK5
% 1.72/0.99      | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),sK7) = iProver_top
% 1.72/0.99      | r1_tmap_1(X0_53,sK1,sK4,sK7) != iProver_top
% 1.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 1.72/0.99      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X2_53) = iProver_top
% 1.72/0.99      | v2_struct_0(sK1) = iProver_top
% 1.72/0.99      | l1_pre_topc(X2_53) != iProver_top
% 1.72/0.99      | l1_pre_topc(sK1) != iProver_top
% 1.72/0.99      | v2_pre_topc(X2_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 1.72/0.99      inference(equality_resolution,[status(thm)],[c_1781]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_28,negated_conjecture,
% 1.72/0.99      ( ~ v2_struct_0(sK1) ),
% 1.72/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_35,plain,
% 1.72/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_27,negated_conjecture,
% 1.72/0.99      ( v2_pre_topc(sK1) ),
% 1.72/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_36,plain,
% 1.72/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_26,negated_conjecture,
% 1.72/0.99      ( l1_pre_topc(sK1) ),
% 1.72/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_37,plain,
% 1.72/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_17,negated_conjecture,
% 1.72/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.72/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_46,plain,
% 1.72/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_16,negated_conjecture,
% 1.72/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.72/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_47,plain,
% 1.72/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1122,plain,( X0_54 = X0_54 ),theory(equality) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2009,plain,
% 1.72/0.99      ( sK7 = sK7 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1122]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2030,plain,
% 1.72/0.99      ( sK5 = sK5 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1122]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1124,plain,
% 1.72/0.99      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 1.72/0.99      theory(equality) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2022,plain,
% 1.72/0.99      ( X0_54 != X1_54 | X0_54 = sK6 | sK6 != X1_54 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1124]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2178,plain,
% 1.72/0.99      ( X0_54 = sK6 | X0_54 != sK7 | sK6 != sK7 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2022]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2232,plain,
% 1.72/0.99      ( sK6 != sK7 | sK7 = sK6 | sK7 != sK7 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2178]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1127,plain,
% 1.72/0.99      ( X0_55 != X1_55 | k1_zfmisc_1(X0_55) = k1_zfmisc_1(X1_55) ),
% 1.72/0.99      theory(equality) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2148,plain,
% 1.72/0.99      ( X0_55 != u1_struct_0(sK3)
% 1.72/0.99      | k1_zfmisc_1(X0_55) = k1_zfmisc_1(u1_struct_0(sK3)) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1127]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2323,plain,
% 1.72/0.99      ( k1_zfmisc_1(u1_struct_0(X0_53)) = k1_zfmisc_1(u1_struct_0(sK3))
% 1.72/0.99      | u1_struct_0(X0_53) != u1_struct_0(sK3) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2148]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1128,plain,
% 1.72/0.99      ( ~ m1_subset_1(X0_54,X0_55)
% 1.72/0.99      | m1_subset_1(X1_54,X1_55)
% 1.72/0.99      | X1_55 != X0_55
% 1.72/0.99      | X1_54 != X0_54 ),
% 1.72/0.99      theory(equality) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1979,plain,
% 1.72/0.99      ( m1_subset_1(X0_54,X0_55)
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.72/0.99      | X0_55 != u1_struct_0(sK3)
% 1.72/0.99      | X0_54 != sK6 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1128]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2520,plain,
% 1.72/0.99      ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.72/0.99      | m1_subset_1(sK7,X0_55)
% 1.72/0.99      | X0_55 != u1_struct_0(sK3)
% 1.72/0.99      | sK7 != sK6 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1979]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2567,plain,
% 1.72/0.99      ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X0_53))
% 1.72/0.99      | u1_struct_0(X0_53) != u1_struct_0(sK3)
% 1.72/0.99      | sK7 != sK6 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2520]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2568,plain,
% 1.72/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 1.72/0.99      | sK7 != sK6
% 1.72/0.99      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X0_53)) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2567]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1984,plain,
% 1.72/0.99      ( m1_subset_1(X0_54,X0_55)
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.72/0.99      | X0_55 != k1_zfmisc_1(u1_struct_0(sK3))
% 1.72/0.99      | X0_54 != sK5 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1128]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2029,plain,
% 1.72/0.99      ( m1_subset_1(sK5,X0_55)
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.72/0.99      | X0_55 != k1_zfmisc_1(u1_struct_0(sK3))
% 1.72/0.99      | sK5 != sK5 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1984]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2725,plain,
% 1.72/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53)))
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.72/0.99      | k1_zfmisc_1(u1_struct_0(X0_53)) != k1_zfmisc_1(u1_struct_0(sK3))
% 1.72/0.99      | sK5 != sK5 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2029]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2727,plain,
% 1.72/0.99      ( k1_zfmisc_1(u1_struct_0(X0_53)) != k1_zfmisc_1(u1_struct_0(sK3))
% 1.72/0.99      | sK5 != sK5
% 1.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53))) = iProver_top
% 1.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2725]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2814,plain,
% 1.72/0.99      ( v2_pre_topc(X2_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X2_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 1.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
% 1.72/0.99      | r1_tmap_1(X0_53,sK1,sK4,sK7) != iProver_top
% 1.72/0.99      | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),sK7) = iProver_top
% 1.72/0.99      | k1_tops_1(X0_53,sK5) != sK5
% 1.72/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK2)
% 1.72/0.99      | u1_struct_0(X0_53) != u1_struct_0(sK3)
% 1.72/0.99      | l1_pre_topc(X2_53) != iProver_top ),
% 1.72/0.99      inference(global_propositional_subsumption,
% 1.72/0.99                [status(thm)],
% 1.72/0.99                [c_2308,c_35,c_36,c_37,c_46,c_47,c_1113,c_2009,c_2030,
% 1.72/0.99                 c_2232,c_2323,c_2568,c_2727]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2815,plain,
% 1.72/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK2)
% 1.72/0.99      | k1_tops_1(X0_53,sK5) != sK5
% 1.72/0.99      | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),sK7) = iProver_top
% 1.72/0.99      | r1_tmap_1(X0_53,sK1,sK4,sK7) != iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 1.72/0.99      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X2_53) = iProver_top
% 1.72/0.99      | l1_pre_topc(X2_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X2_53) != iProver_top ),
% 1.72/0.99      inference(renaming,[status(thm)],[c_2814]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2834,plain,
% 1.72/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK2)
% 1.72/0.99      | k1_tops_1(sK3,sK5) != sK5
% 1.72/0.99      | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),sK7) = iProver_top
% 1.72/0.99      | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,sK3) != iProver_top
% 1.72/0.99      | m1_pre_topc(sK3,X1_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | v2_struct_0(sK3) = iProver_top
% 1.72/0.99      | l1_pre_topc(X1_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X1_53) != iProver_top ),
% 1.72/0.99      inference(equality_resolution,[status(thm)],[c_2815]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_3,plain,
% 1.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.72/0.99      | ~ v3_pre_topc(X0,X1)
% 1.72/0.99      | ~ l1_pre_topc(X3)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X3)
% 1.72/0.99      | k1_tops_1(X1,X0) = X0 ),
% 1.72/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_14,negated_conjecture,
% 1.72/0.99      ( v3_pre_topc(sK5,sK3) ),
% 1.72/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_386,plain,
% 1.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X3)
% 1.72/0.99      | ~ v2_pre_topc(X3)
% 1.72/0.99      | k1_tops_1(X1,X0) = X0
% 1.72/0.99      | sK5 != X0
% 1.72/0.99      | sK3 != X1 ),
% 1.72/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_14]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_387,plain,
% 1.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(sK3)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | k1_tops_1(sK3,sK5) = sK5 ),
% 1.72/0.99      inference(unflattening,[status(thm)],[c_386]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_391,plain,
% 1.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(sK3)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | k1_tops_1(sK3,sK5) = sK5 ),
% 1.72/0.99      inference(global_propositional_subsumption,
% 1.72/0.99                [status(thm)],
% 1.72/0.99                [c_387,c_17]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1097,plain,
% 1.72/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 1.72/0.99      | ~ l1_pre_topc(X0_53)
% 1.72/0.99      | ~ l1_pre_topc(sK3)
% 1.72/0.99      | ~ v2_pre_topc(X0_53)
% 1.72/0.99      | k1_tops_1(sK3,sK5) = sK5 ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_391]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1120,plain,
% 1.72/0.99      ( ~ l1_pre_topc(sK3)
% 1.72/0.99      | sP0_iProver_split
% 1.72/0.99      | k1_tops_1(sK3,sK5) = sK5 ),
% 1.72/0.99      inference(splitting,
% 1.72/0.99                [splitting(split),new_symbols(definition,[])],
% 1.72/0.99                [c_1097]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1696,plain,
% 1.72/0.99      ( k1_tops_1(sK3,sK5) = sK5
% 1.72/0.99      | l1_pre_topc(sK3) != iProver_top
% 1.72/0.99      | sP0_iProver_split = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1120]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_30,negated_conjecture,
% 1.72/0.99      ( v2_pre_topc(sK0) ),
% 1.72/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_29,negated_conjecture,
% 1.72/0.99      ( l1_pre_topc(sK0) ),
% 1.72/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_22,negated_conjecture,
% 1.72/0.99      ( m1_pre_topc(sK3,sK0) ),
% 1.72/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1117,plain,
% 1.72/0.99      ( ~ m1_pre_topc(X0_53,X1_53)
% 1.72/0.99      | ~ l1_pre_topc(X1_53)
% 1.72/0.99      | l1_pre_topc(X0_53) ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1949,plain,
% 1.72/0.99      ( ~ m1_pre_topc(X0_53,sK0)
% 1.72/0.99      | l1_pre_topc(X0_53)
% 1.72/0.99      | ~ l1_pre_topc(sK0) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1117]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1951,plain,
% 1.72/0.99      ( ~ m1_pre_topc(sK3,sK0) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK0) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1949]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1118,plain,
% 1.72/0.99      ( ~ m1_pre_topc(X0_53,X1_53)
% 1.72/0.99      | ~ l1_pre_topc(X1_53)
% 1.72/0.99      | ~ v2_pre_topc(X1_53)
% 1.72/0.99      | v2_pre_topc(X0_53) ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1959,plain,
% 1.72/0.99      ( ~ m1_pre_topc(X0_53,sK0)
% 1.72/0.99      | ~ l1_pre_topc(sK0)
% 1.72/0.99      | v2_pre_topc(X0_53)
% 1.72/0.99      | ~ v2_pre_topc(sK0) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1118]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1961,plain,
% 1.72/0.99      ( ~ m1_pre_topc(sK3,sK0)
% 1.72/0.99      | ~ l1_pre_topc(sK0)
% 1.72/0.99      | v2_pre_topc(sK3)
% 1.72/0.99      | ~ v2_pre_topc(sK0) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1959]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1119,plain,
% 1.72/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 1.72/0.99      | ~ l1_pre_topc(X0_53)
% 1.72/0.99      | ~ v2_pre_topc(X0_53)
% 1.72/0.99      | ~ sP0_iProver_split ),
% 1.72/0.99      inference(splitting,
% 1.72/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.72/0.99                [c_1097]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2234,plain,
% 1.72/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.72/0.99      | ~ l1_pre_topc(sK3)
% 1.72/0.99      | ~ v2_pre_topc(sK3)
% 1.72/0.99      | ~ sP0_iProver_split ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1119]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2757,plain,
% 1.72/0.99      ( k1_tops_1(sK3,sK5) = sK5 ),
% 1.72/0.99      inference(global_propositional_subsumption,
% 1.72/0.99                [status(thm)],
% 1.72/0.99                [c_1696,c_30,c_29,c_22,c_17,c_1120,c_1951,c_1961,c_2234]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2835,plain,
% 1.72/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK2)
% 1.72/0.99      | sK5 != sK5
% 1.72/0.99      | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),sK7) = iProver_top
% 1.72/0.99      | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,sK3) != iProver_top
% 1.72/0.99      | m1_pre_topc(sK3,X1_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | v2_struct_0(sK3) = iProver_top
% 1.72/0.99      | l1_pre_topc(X1_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X1_53) != iProver_top ),
% 1.72/0.99      inference(light_normalisation,[status(thm)],[c_2834,c_2757]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2836,plain,
% 1.72/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK2)
% 1.72/0.99      | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),sK7) = iProver_top
% 1.72/0.99      | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,sK3) != iProver_top
% 1.72/0.99      | m1_pre_topc(sK3,X1_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | v2_struct_0(sK3) = iProver_top
% 1.72/0.99      | l1_pre_topc(X1_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X1_53) != iProver_top ),
% 1.72/0.99      inference(equality_resolution_simp,[status(thm)],[c_2835]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_31,negated_conjecture,
% 1.72/0.99      ( ~ v2_struct_0(sK0) ),
% 1.72/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_32,plain,
% 1.72/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_33,plain,
% 1.72/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_34,plain,
% 1.72/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_25,negated_conjecture,
% 1.72/0.99      ( ~ v2_struct_0(sK2) ),
% 1.72/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_38,plain,
% 1.72/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_23,negated_conjecture,
% 1.72/0.99      ( ~ v2_struct_0(sK3) ),
% 1.72/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_40,plain,
% 1.72/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_41,plain,
% 1.72/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_19,negated_conjecture,
% 1.72/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 1.72/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_44,plain,
% 1.72/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_18,negated_conjecture,
% 1.72/0.99      ( m1_pre_topc(sK2,sK3) ),
% 1.72/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_45,plain,
% 1.72/0.99      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_15,negated_conjecture,
% 1.72/0.99      ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
% 1.72/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_48,plain,
% 1.72/0.99      ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1139,plain,
% 1.72/0.99      ( sK4 = sK4 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1122]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_10,negated_conjecture,
% 1.72/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK6)
% 1.72/0.99      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 1.72/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1114,negated_conjecture,
% 1.72/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK6)
% 1.72/0.99      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1680,plain,
% 1.72/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK6) = iProver_top
% 1.72/0.99      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1114]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1745,plain,
% 1.72/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 1.72/0.99      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
% 1.72/0.99      inference(light_normalisation,[status(thm)],[c_1680,c_1113]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1123,plain,( X0_55 = X0_55 ),theory(equality) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2058,plain,
% 1.72/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1123]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2091,plain,
% 1.72/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1123]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1974,plain,
% 1.72/0.99      ( m1_subset_1(X0_54,X0_55)
% 1.72/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK2))
% 1.72/0.99      | X0_55 != u1_struct_0(sK2)
% 1.72/0.99      | X0_54 != sK7 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1128]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2003,plain,
% 1.72/0.99      ( m1_subset_1(sK6,X0_55)
% 1.72/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK2))
% 1.72/0.99      | X0_55 != u1_struct_0(sK2)
% 1.72/0.99      | sK6 != sK7 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1974]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2104,plain,
% 1.72/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2))
% 1.72/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK2))
% 1.72/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.72/0.99      | sK6 != sK7 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2003]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2106,plain,
% 1.72/0.99      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.72/0.99      | sK6 != sK7
% 1.72/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2104]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2105,plain,
% 1.72/0.99      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1123]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1129,plain,
% 1.72/0.99      ( ~ r1_tmap_1(X0_53,X1_53,X0_54,X1_54)
% 1.72/0.99      | r1_tmap_1(X0_53,X1_53,X2_54,X3_54)
% 1.72/0.99      | X2_54 != X0_54
% 1.72/0.99      | X3_54 != X1_54 ),
% 1.72/0.99      theory(equality) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1994,plain,
% 1.72/0.99      ( r1_tmap_1(sK2,sK1,X0_54,X1_54)
% 1.72/0.99      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
% 1.72/0.99      | X0_54 != k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
% 1.72/0.99      | X1_54 != sK7 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1129]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2050,plain,
% 1.72/0.99      ( r1_tmap_1(sK2,sK1,X0_54,sK6)
% 1.72/0.99      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
% 1.72/0.99      | X0_54 != k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
% 1.72/0.99      | sK6 != sK7 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1994]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2110,plain,
% 1.72/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
% 1.72/0.99      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
% 1.72/0.99      | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) != k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
% 1.72/0.99      | sK6 != sK7 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2050]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2112,plain,
% 1.72/0.99      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) != k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
% 1.72/0.99      | sK6 != sK7
% 1.72/0.99      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top
% 1.72/0.99      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2110]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2111,plain,
% 1.72/0.99      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1122]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2254,plain,
% 1.72/0.99      ( r1_tmap_1(sK3,sK1,X0_54,X1_54)
% 1.72/0.99      | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
% 1.72/0.99      | X1_54 != sK6
% 1.72/0.99      | X0_54 != sK4 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1129]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2529,plain,
% 1.72/0.99      ( r1_tmap_1(sK3,sK1,X0_54,sK7)
% 1.72/0.99      | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
% 1.72/0.99      | X0_54 != sK4
% 1.72/0.99      | sK7 != sK6 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2254]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2530,plain,
% 1.72/0.99      ( X0_54 != sK4
% 1.72/0.99      | sK7 != sK6
% 1.72/0.99      | r1_tmap_1(sK3,sK1,X0_54,sK7) = iProver_top
% 1.72/0.99      | r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2529]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2532,plain,
% 1.72/0.99      ( sK7 != sK6
% 1.72/0.99      | sK4 != sK4
% 1.72/0.99      | r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top
% 1.72/0.99      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2530]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_7,plain,
% 1.72/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.72/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.72/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.72/0.99      | ~ m1_connsp_2(X6,X0,X3)
% 1.72/0.99      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_pre_topc(X4,X0)
% 1.72/0.99      | ~ m1_pre_topc(X0,X5)
% 1.72/0.99      | ~ m1_pre_topc(X4,X5)
% 1.72/0.99      | ~ v1_funct_1(X2)
% 1.72/0.99      | v2_struct_0(X5)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X4)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | ~ l1_pre_topc(X5)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X5)
% 1.72/0.99      | ~ v2_pre_topc(X1) ),
% 1.72/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_524,plain,
% 1.72/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.72/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.72/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.72/0.99      | ~ m1_connsp_2(X6,X0,X3)
% 1.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_pre_topc(X4,X0)
% 1.72/0.99      | ~ m1_pre_topc(X0,X5)
% 1.72/0.99      | ~ m1_pre_topc(X4,X5)
% 1.72/0.99      | ~ v1_funct_1(X2)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X5)
% 1.72/0.99      | v2_struct_0(X4)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X5)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X5)
% 1.72/0.99      | u1_struct_0(X4) != u1_struct_0(sK2)
% 1.72/0.99      | sK5 != X6 ),
% 1.72/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_525,plain,
% 1.72/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.72/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.72/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.72/0.99      | ~ m1_connsp_2(sK5,X0,X3)
% 1.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.72/0.99      | ~ m1_pre_topc(X4,X0)
% 1.72/0.99      | ~ m1_pre_topc(X0,X5)
% 1.72/0.99      | ~ m1_pre_topc(X4,X5)
% 1.72/0.99      | ~ v1_funct_1(X2)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X5)
% 1.72/0.99      | v2_struct_0(X4)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X5)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X5)
% 1.72/0.99      | u1_struct_0(X4) != u1_struct_0(sK2) ),
% 1.72/0.99      inference(unflattening,[status(thm)],[c_524]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_571,plain,
% 1.72/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.72/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.72/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.72/0.99      | ~ m1_connsp_2(sK5,X0,X3)
% 1.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.72/0.99      | ~ m1_pre_topc(X4,X0)
% 1.72/0.99      | ~ m1_pre_topc(X0,X5)
% 1.72/0.99      | ~ v1_funct_1(X2)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X5)
% 1.72/0.99      | v2_struct_0(X4)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X5)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X5)
% 1.72/0.99      | u1_struct_0(X4) != u1_struct_0(sK2) ),
% 1.72/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_525,c_6]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_595,plain,
% 1.72/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.72/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.72/0.99      | ~ m1_connsp_2(sK5,X0,X3)
% 1.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.72/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.72/0.99      | ~ m1_pre_topc(X4,X0)
% 1.72/0.99      | ~ m1_pre_topc(X0,X5)
% 1.72/0.99      | ~ v1_funct_1(X2)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X5)
% 1.72/0.99      | v2_struct_0(X4)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X5)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X5)
% 1.72/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X4) != u1_struct_0(sK2)
% 1.72/0.99      | sK4 != X2 ),
% 1.72/0.99      inference(resolution_lifted,[status(thm)],[c_571,c_20]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_596,plain,
% 1.72/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.72/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 1.72/0.99      | ~ m1_connsp_2(sK5,X3,X4)
% 1.72/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_pre_topc(X0,X3)
% 1.72/0.99      | ~ m1_pre_topc(X3,X2)
% 1.72/0.99      | ~ v1_funct_1(sK4)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X3)
% 1.72/0.99      | v2_struct_0(X2)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X2)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X2)
% 1.72/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.72/0.99      inference(unflattening,[status(thm)],[c_595]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_600,plain,
% 1.72/0.99      ( ~ m1_pre_topc(X3,X2)
% 1.72/0.99      | ~ m1_pre_topc(X0,X3)
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.72/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.72/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_connsp_2(sK5,X3,X4)
% 1.72/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 1.72/0.99      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X3)
% 1.72/0.99      | v2_struct_0(X2)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X2)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X2)
% 1.72/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.72/0.99      inference(global_propositional_subsumption,
% 1.72/0.99                [status(thm)],
% 1.72/0.99                [c_596,c_21]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_601,plain,
% 1.72/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.72/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 1.72/0.99      | ~ m1_connsp_2(sK5,X3,X4)
% 1.72/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_pre_topc(X0,X3)
% 1.72/0.99      | ~ m1_pre_topc(X3,X2)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X2)
% 1.72/0.99      | v2_struct_0(X3)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X2)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X2)
% 1.72/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.72/0.99      inference(renaming,[status(thm)],[c_600]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_812,plain,
% 1.72/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.72/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 1.72/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X6)))
% 1.72/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X6))
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_pre_topc(X0,X3)
% 1.72/0.99      | ~ m1_pre_topc(X3,X2)
% 1.72/0.99      | v2_struct_0(X6)
% 1.72/0.99      | v2_struct_0(X3)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X2)
% 1.72/0.99      | ~ l1_pre_topc(X6)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X2)
% 1.72/0.99      | ~ v2_pre_topc(X6)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X2)
% 1.72/0.99      | X3 != X6
% 1.72/0.99      | k1_tops_1(X6,X5) != sK5
% 1.72/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.72/0.99      | sK5 != X5
% 1.72/0.99      | sK6 != X4 ),
% 1.72/0.99      inference(resolution_lifted,[status(thm)],[c_421,c_601]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_813,plain,
% 1.72/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 1.72/0.99      | r1_tmap_1(X3,X1,sK4,sK6)
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_pre_topc(X0,X3)
% 1.72/0.99      | ~ m1_pre_topc(X3,X2)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X2)
% 1.72/0.99      | v2_struct_0(X3)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X2)
% 1.72/0.99      | ~ l1_pre_topc(X3)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X2)
% 1.72/0.99      | ~ v2_pre_topc(X3)
% 1.72/0.99      | k1_tops_1(X3,sK5) != sK5
% 1.72/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.72/0.99      inference(unflattening,[status(thm)],[c_812]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_861,plain,
% 1.72/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 1.72/0.99      | r1_tmap_1(X3,X1,sK4,sK6)
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.72/0.99      | ~ m1_pre_topc(X0,X3)
% 1.72/0.99      | ~ m1_pre_topc(X3,X2)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X2)
% 1.72/0.99      | v2_struct_0(X3)
% 1.72/0.99      | ~ l1_pre_topc(X1)
% 1.72/0.99      | ~ l1_pre_topc(X2)
% 1.72/0.99      | ~ v2_pre_topc(X1)
% 1.72/0.99      | ~ v2_pre_topc(X2)
% 1.72/0.99      | k1_tops_1(X3,sK5) != sK5
% 1.72/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.72/0.99      inference(forward_subsumption_resolution,
% 1.72/0.99                [status(thm)],
% 1.72/0.99                [c_813,c_0,c_1]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1095,plain,
% 1.72/0.99      ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),sK6)
% 1.72/0.99      | r1_tmap_1(X3_53,X1_53,sK4,sK6)
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_53)))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3_53))
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
% 1.72/0.99      | ~ m1_pre_topc(X0_53,X3_53)
% 1.72/0.99      | ~ m1_pre_topc(X3_53,X2_53)
% 1.72/0.99      | v2_struct_0(X1_53)
% 1.72/0.99      | v2_struct_0(X0_53)
% 1.72/0.99      | v2_struct_0(X2_53)
% 1.72/0.99      | v2_struct_0(X3_53)
% 1.72/0.99      | ~ l1_pre_topc(X1_53)
% 1.72/0.99      | ~ l1_pre_topc(X2_53)
% 1.72/0.99      | ~ v2_pre_topc(X1_53)
% 1.72/0.99      | ~ v2_pre_topc(X2_53)
% 1.72/0.99      | u1_struct_0(X3_53) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X0_53) != u1_struct_0(sK2)
% 1.72/0.99      | k1_tops_1(X3_53,sK5) != sK5 ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_861]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2090,plain,
% 1.72/0.99      ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,sK3,X0_53,sK4),sK6)
% 1.72/0.99      | r1_tmap_1(sK3,X1_53,sK4,sK6)
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
% 1.72/0.99      | ~ m1_pre_topc(X0_53,sK3)
% 1.72/0.99      | ~ m1_pre_topc(sK3,X2_53)
% 1.72/0.99      | v2_struct_0(X1_53)
% 1.72/0.99      | v2_struct_0(X0_53)
% 1.72/0.99      | v2_struct_0(X2_53)
% 1.72/0.99      | v2_struct_0(sK3)
% 1.72/0.99      | ~ l1_pre_topc(X1_53)
% 1.72/0.99      | ~ l1_pre_topc(X2_53)
% 1.72/0.99      | ~ v2_pre_topc(X1_53)
% 1.72/0.99      | ~ v2_pre_topc(X2_53)
% 1.72/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X0_53) != u1_struct_0(sK2)
% 1.72/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.72/0.99      | k1_tops_1(sK3,sK5) != sK5 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1095]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2223,plain,
% 1.72/0.99      ( r1_tmap_1(sK3,X0_53,sK4,sK6)
% 1.72/0.99      | ~ r1_tmap_1(sK2,X0_53,k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4),sK6)
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 1.72/0.99      | ~ m1_pre_topc(sK3,X1_53)
% 1.72/0.99      | ~ m1_pre_topc(sK2,sK3)
% 1.72/0.99      | v2_struct_0(X1_53)
% 1.72/0.99      | v2_struct_0(X0_53)
% 1.72/0.99      | v2_struct_0(sK3)
% 1.72/0.99      | v2_struct_0(sK2)
% 1.72/0.99      | ~ l1_pre_topc(X1_53)
% 1.72/0.99      | ~ l1_pre_topc(X0_53)
% 1.72/0.99      | ~ v2_pre_topc(X1_53)
% 1.72/0.99      | ~ v2_pre_topc(X0_53)
% 1.72/0.99      | u1_struct_0(X0_53) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.72/0.99      | k1_tops_1(sK3,sK5) != sK5 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2090]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2514,plain,
% 1.72/0.99      ( r1_tmap_1(sK3,X0_53,sK4,sK6)
% 1.72/0.99      | ~ r1_tmap_1(sK2,X0_53,k3_tmap_1(sK0,X0_53,sK3,sK2,sK4),sK6)
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 1.72/0.99      | ~ m1_pre_topc(sK3,sK0)
% 1.72/0.99      | ~ m1_pre_topc(sK2,sK3)
% 1.72/0.99      | v2_struct_0(X0_53)
% 1.72/0.99      | v2_struct_0(sK3)
% 1.72/0.99      | v2_struct_0(sK0)
% 1.72/0.99      | v2_struct_0(sK2)
% 1.72/0.99      | ~ l1_pre_topc(X0_53)
% 1.72/0.99      | ~ l1_pre_topc(sK0)
% 1.72/0.99      | ~ v2_pre_topc(X0_53)
% 1.72/0.99      | ~ v2_pre_topc(sK0)
% 1.72/0.99      | u1_struct_0(X0_53) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.72/0.99      | k1_tops_1(sK3,sK5) != sK5 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2223]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2558,plain,
% 1.72/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK6)
% 1.72/0.99      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
% 1.72/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.72/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 1.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 1.72/0.99      | ~ m1_pre_topc(sK3,sK0)
% 1.72/0.99      | ~ m1_pre_topc(sK2,sK3)
% 1.72/0.99      | v2_struct_0(sK3)
% 1.72/0.99      | v2_struct_0(sK0)
% 1.72/0.99      | v2_struct_0(sK1)
% 1.72/0.99      | v2_struct_0(sK2)
% 1.72/0.99      | ~ l1_pre_topc(sK0)
% 1.72/0.99      | ~ l1_pre_topc(sK1)
% 1.72/0.99      | ~ v2_pre_topc(sK0)
% 1.72/0.99      | ~ v2_pre_topc(sK1)
% 1.72/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.72/0.99      | k1_tops_1(sK3,sK5) != sK5 ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2514]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2559,plain,
% 1.72/0.99      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.72/0.99      | k1_tops_1(sK3,sK5) != sK5
% 1.72/0.99      | r1_tmap_1(sK3,sK1,sK4,sK6) = iProver_top
% 1.72/0.99      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) != iProver_top
% 1.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.72/0.99      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.72/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 1.72/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 1.72/0.99      | v2_struct_0(sK3) = iProver_top
% 1.72/0.99      | v2_struct_0(sK0) = iProver_top
% 1.72/0.99      | v2_struct_0(sK1) = iProver_top
% 1.72/0.99      | v2_struct_0(sK2) = iProver_top
% 1.72/0.99      | l1_pre_topc(sK0) != iProver_top
% 1.72/0.99      | l1_pre_topc(sK1) != iProver_top
% 1.72/0.99      | v2_pre_topc(sK0) != iProver_top
% 1.72/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2558]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2893,plain,
% 1.72/0.99      ( v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | m1_pre_topc(sK3,X1_53) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,sK3) != iProver_top
% 1.72/0.99      | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),sK7) = iProver_top
% 1.72/0.99      | u1_struct_0(X0_53) != u1_struct_0(sK2)
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 1.72/0.99      | l1_pre_topc(X1_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X1_53) != iProver_top ),
% 1.72/0.99      inference(global_propositional_subsumption,
% 1.72/0.99                [status(thm)],
% 1.72/0.99                [c_2836,c_32,c_30,c_33,c_29,c_34,c_35,c_36,c_37,c_38,
% 1.72/0.99                 c_40,c_22,c_41,c_44,c_45,c_17,c_46,c_47,c_48,c_1139,
% 1.72/0.99                 c_1113,c_1120,c_1745,c_1951,c_1961,c_2009,c_2058,c_2091,
% 1.72/0.99                 c_2106,c_2105,c_2112,c_2111,c_2232,c_2234,c_2532,c_2559]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2894,plain,
% 1.72/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK2)
% 1.72/0.99      | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),sK7) = iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,sK3) != iProver_top
% 1.72/0.99      | m1_pre_topc(sK3,X1_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | l1_pre_topc(X1_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X1_53) != iProver_top ),
% 1.72/0.99      inference(renaming,[status(thm)],[c_2893]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2908,plain,
% 1.72/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(X0_53,sK1,sK3,sK2,sK4),sK7) = iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
% 1.72/0.99      | m1_pre_topc(sK3,X0_53) != iProver_top
% 1.72/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | v2_struct_0(sK2) = iProver_top
% 1.72/0.99      | l1_pre_topc(X0_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X0_53) != iProver_top ),
% 1.72/0.99      inference(equality_resolution,[status(thm)],[c_2894]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2992,plain,
% 1.72/0.99      ( v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | r1_tmap_1(sK2,sK1,k3_tmap_1(X0_53,sK1,sK3,sK2,sK4),sK7) = iProver_top
% 1.72/0.99      | m1_pre_topc(sK3,X0_53) != iProver_top
% 1.72/0.99      | l1_pre_topc(X0_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X0_53) != iProver_top ),
% 1.72/0.99      inference(global_propositional_subsumption,
% 1.72/0.99                [status(thm)],
% 1.72/0.99                [c_2908,c_38,c_45,c_48]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2993,plain,
% 1.72/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(X0_53,sK1,sK3,sK2,sK4),sK7) = iProver_top
% 1.72/0.99      | m1_pre_topc(sK3,X0_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | l1_pre_topc(X0_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X0_53) != iProver_top ),
% 1.72/0.99      inference(renaming,[status(thm)],[c_2992]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_9,negated_conjecture,
% 1.72/0.99      ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
% 1.72/0.99      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 1.72/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1115,negated_conjecture,
% 1.72/0.99      ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
% 1.72/0.99      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1679,plain,
% 1.72/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top
% 1.72/0.99      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1115]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1750,plain,
% 1.72/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 1.72/0.99      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
% 1.72/0.99      inference(light_normalisation,[status(thm)],[c_1679,c_1113]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_3003,plain,
% 1.72/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 1.72/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 1.72/0.99      | v2_struct_0(sK0) = iProver_top
% 1.72/0.99      | l1_pre_topc(sK0) != iProver_top
% 1.72/0.99      | v2_pre_topc(sK0) != iProver_top ),
% 1.72/0.99      inference(superposition,[status(thm)],[c_2993,c_1750]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1699,plain,
% 1.72/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X2_53) != u1_struct_0(sK2)
% 1.72/0.99      | k1_tops_1(X0_53,sK5) != sK5
% 1.72/0.99      | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4),sK6) != iProver_top
% 1.72/0.99      | r1_tmap_1(X0_53,X1_53,sK4,sK6) = iProver_top
% 1.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 1.72/0.99      | m1_subset_1(sK6,u1_struct_0(X2_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK6,u1_struct_0(X0_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 1.72/0.99      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X2_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X3_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | l1_pre_topc(X1_53) != iProver_top
% 1.72/0.99      | l1_pre_topc(X3_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X1_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X3_53) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1095]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1822,plain,
% 1.72/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 1.72/0.99      | u1_struct_0(X2_53) != u1_struct_0(sK2)
% 1.72/0.99      | k1_tops_1(X0_53,sK5) != sK5
% 1.72/0.99      | r1_tmap_1(X2_53,X1_53,k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4),sK7) != iProver_top
% 1.72/0.99      | r1_tmap_1(X0_53,X1_53,sK4,sK7) = iProver_top
% 1.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X2_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 1.72/0.99      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X2_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X3_53) = iProver_top
% 1.72/0.99      | l1_pre_topc(X1_53) != iProver_top
% 1.72/0.99      | l1_pre_topc(X3_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X1_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X3_53) != iProver_top ),
% 1.72/0.99      inference(light_normalisation,[status(thm)],[c_1699,c_1113]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2364,plain,
% 1.72/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK2)
% 1.72/0.99      | k1_tops_1(X0_53,sK5) != sK5
% 1.72/0.99      | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),sK7) != iProver_top
% 1.72/0.99      | r1_tmap_1(X0_53,sK1,sK4,sK7) = iProver_top
% 1.72/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 1.72/0.99      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X2_53) = iProver_top
% 1.72/0.99      | v2_struct_0(sK1) = iProver_top
% 1.72/0.99      | l1_pre_topc(X2_53) != iProver_top
% 1.72/0.99      | l1_pre_topc(sK1) != iProver_top
% 1.72/0.99      | v2_pre_topc(X2_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 1.72/0.99      inference(equality_resolution,[status(thm)],[c_1822]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2841,plain,
% 1.72/0.99      ( v2_pre_topc(X2_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X2_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 1.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
% 1.72/0.99      | r1_tmap_1(X0_53,sK1,sK4,sK7) = iProver_top
% 1.72/0.99      | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),sK7) != iProver_top
% 1.72/0.99      | k1_tops_1(X0_53,sK5) != sK5
% 1.72/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK2)
% 1.72/0.99      | u1_struct_0(X0_53) != u1_struct_0(sK3)
% 1.72/0.99      | l1_pre_topc(X2_53) != iProver_top ),
% 1.72/0.99      inference(global_propositional_subsumption,
% 1.72/0.99                [status(thm)],
% 1.72/0.99                [c_2364,c_35,c_36,c_37,c_46,c_47,c_1113,c_2009,c_2030,
% 1.72/0.99                 c_2232,c_2323,c_2568,c_2727]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2842,plain,
% 1.72/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 1.72/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK2)
% 1.72/0.99      | k1_tops_1(X0_53,sK5) != sK5
% 1.72/0.99      | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),sK7) != iProver_top
% 1.72/0.99      | r1_tmap_1(X0_53,sK1,sK4,sK7) = iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X1_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 1.72/0.99      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X2_53) = iProver_top
% 1.72/0.99      | l1_pre_topc(X2_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X2_53) != iProver_top ),
% 1.72/0.99      inference(renaming,[status(thm)],[c_2841]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2861,plain,
% 1.72/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK2)
% 1.72/0.99      | k1_tops_1(sK3,sK5) != sK5
% 1.72/0.99      | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),sK7) != iProver_top
% 1.72/0.99      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,sK3) != iProver_top
% 1.72/0.99      | m1_pre_topc(sK3,X1_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | v2_struct_0(sK3) = iProver_top
% 1.72/0.99      | l1_pre_topc(X1_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X1_53) != iProver_top ),
% 1.72/0.99      inference(equality_resolution,[status(thm)],[c_2842]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2862,plain,
% 1.72/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK2)
% 1.72/0.99      | sK5 != sK5
% 1.72/0.99      | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),sK7) != iProver_top
% 1.72/0.99      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,sK3) != iProver_top
% 1.72/0.99      | m1_pre_topc(sK3,X1_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | v2_struct_0(sK3) = iProver_top
% 1.72/0.99      | l1_pre_topc(X1_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X1_53) != iProver_top ),
% 1.72/0.99      inference(light_normalisation,[status(thm)],[c_2861,c_2757]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2863,plain,
% 1.72/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK2)
% 1.72/0.99      | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),sK7) != iProver_top
% 1.72/0.99      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 1.72/0.99      | m1_subset_1(sK7,u1_struct_0(X0_53)) != iProver_top
% 1.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.72/0.99      | m1_pre_topc(X0_53,sK3) != iProver_top
% 1.72/0.99      | m1_pre_topc(sK3,X1_53) != iProver_top
% 1.72/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.72/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.72/0.99      | v2_struct_0(sK3) = iProver_top
% 1.72/0.99      | l1_pre_topc(X1_53) != iProver_top
% 1.72/0.99      | v2_pre_topc(X1_53) != iProver_top ),
% 1.72/0.99      inference(equality_resolution_simp,[status(thm)],[c_2862]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2913,plain,
% 1.72/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top ),
% 1.72/0.99      inference(global_propositional_subsumption,
% 1.72/0.99                [status(thm)],
% 1.72/0.99                [c_2863,c_32,c_30,c_33,c_29,c_34,c_35,c_36,c_37,c_38,
% 1.72/0.99                 c_40,c_22,c_41,c_44,c_45,c_17,c_46,c_47,c_48,c_1139,
% 1.72/0.99                 c_1113,c_1120,c_1745,c_1951,c_1961,c_2009,c_2058,c_2091,
% 1.72/0.99                 c_2106,c_2105,c_2112,c_2111,c_2232,c_2234,c_2532,c_2559]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(contradiction,plain,
% 1.72/0.99      ( $false ),
% 1.72/0.99      inference(minisat,[status(thm)],[c_3003,c_2913,c_41,c_34,c_33,c_32]) ).
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.72/0.99  
% 1.72/0.99  ------                               Statistics
% 1.72/0.99  
% 1.72/0.99  ------ General
% 1.72/0.99  
% 1.72/0.99  abstr_ref_over_cycles:                  0
% 1.72/0.99  abstr_ref_under_cycles:                 0
% 1.72/0.99  gc_basic_clause_elim:                   0
% 1.72/0.99  forced_gc_time:                         0
% 1.72/0.99  parsing_time:                           0.011
% 1.72/0.99  unif_index_cands_time:                  0.
% 1.72/0.99  unif_index_add_time:                    0.
% 1.72/0.99  orderings_time:                         0.
% 1.72/0.99  out_proof_time:                         0.016
% 1.72/0.99  total_time:                             0.15
% 1.72/0.99  num_of_symbols:                         60
% 1.72/0.99  num_of_terms:                           2070
% 1.72/0.99  
% 1.72/0.99  ------ Preprocessing
% 1.72/0.99  
% 1.72/0.99  num_of_splits:                          1
% 1.72/0.99  num_of_split_atoms:                     1
% 1.72/0.99  num_of_reused_defs:                     0
% 1.72/0.99  num_eq_ax_congr_red:                    18
% 1.72/0.99  num_of_sem_filtered_clauses:            1
% 1.72/0.99  num_of_subtypes:                        3
% 1.72/0.99  monotx_restored_types:                  0
% 1.72/0.99  sat_num_of_epr_types:                   0
% 1.72/0.99  sat_num_of_non_cyclic_types:            0
% 1.72/0.99  sat_guarded_non_collapsed_types:        0
% 1.72/0.99  num_pure_diseq_elim:                    0
% 1.72/0.99  simp_replaced_by:                       0
% 1.72/0.99  res_preprocessed:                       127
% 1.72/0.99  prep_upred:                             0
% 1.72/0.99  prep_unflattend:                        15
% 1.72/0.99  smt_new_axioms:                         0
% 1.72/0.99  pred_elim_cands:                        6
% 1.72/0.99  pred_elim:                              6
% 1.72/0.99  pred_elim_cl:                           8
% 1.72/0.99  pred_elim_cycles:                       8
% 1.72/0.99  merged_defs:                            8
% 1.72/0.99  merged_defs_ncl:                        0
% 1.72/0.99  bin_hyper_res:                          8
% 1.72/0.99  prep_cycles:                            4
% 1.72/0.99  pred_elim_time:                         0.021
% 1.72/0.99  splitting_time:                         0.
% 1.72/0.99  sem_filter_time:                        0.
% 1.72/0.99  monotx_time:                            0.
% 1.72/0.99  subtype_inf_time:                       0.
% 1.72/0.99  
% 1.72/0.99  ------ Problem properties
% 1.72/0.99  
% 1.72/0.99  clauses:                                25
% 1.72/0.99  conjectures:                            18
% 1.72/0.99  epr:                                    15
% 1.72/0.99  horn:                                   21
% 1.72/0.99  ground:                                 19
% 1.72/0.99  unary:                                  16
% 1.72/0.99  binary:                                 2
% 1.72/0.99  lits:                                   79
% 1.72/0.99  lits_eq:                                10
% 1.72/0.99  fd_pure:                                0
% 1.72/0.99  fd_pseudo:                              0
% 1.72/0.99  fd_cond:                                0
% 1.72/0.99  fd_pseudo_cond:                         0
% 1.72/0.99  ac_symbols:                             0
% 1.72/0.99  
% 1.72/0.99  ------ Propositional Solver
% 1.72/0.99  
% 1.72/0.99  prop_solver_calls:                      28
% 1.72/0.99  prop_fast_solver_calls:                 1205
% 1.72/0.99  smt_solver_calls:                       0
% 1.72/0.99  smt_fast_solver_calls:                  0
% 1.72/0.99  prop_num_of_clauses:                    625
% 1.72/0.99  prop_preprocess_simplified:             3100
% 1.72/0.99  prop_fo_subsumed:                       50
% 1.72/0.99  prop_solver_time:                       0.
% 1.72/0.99  smt_solver_time:                        0.
% 1.72/0.99  smt_fast_solver_time:                   0.
% 1.72/0.99  prop_fast_solver_time:                  0.
% 1.72/0.99  prop_unsat_core_time:                   0.
% 1.72/0.99  
% 1.72/0.99  ------ QBF
% 1.72/0.99  
% 1.72/0.99  qbf_q_res:                              0
% 1.72/0.99  qbf_num_tautologies:                    0
% 1.72/0.99  qbf_prep_cycles:                        0
% 1.72/0.99  
% 1.72/0.99  ------ BMC1
% 1.72/0.99  
% 1.72/0.99  bmc1_current_bound:                     -1
% 1.72/0.99  bmc1_last_solved_bound:                 -1
% 1.72/0.99  bmc1_unsat_core_size:                   -1
% 1.72/0.99  bmc1_unsat_core_parents_size:           -1
% 1.72/0.99  bmc1_merge_next_fun:                    0
% 1.72/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.72/0.99  
% 1.72/0.99  ------ Instantiation
% 1.72/0.99  
% 1.72/0.99  inst_num_of_clauses:                    202
% 1.72/0.99  inst_num_in_passive:                    13
% 1.72/0.99  inst_num_in_active:                     168
% 1.72/0.99  inst_num_in_unprocessed:                21
% 1.72/0.99  inst_num_of_loops:                      190
% 1.72/0.99  inst_num_of_learning_restarts:          0
% 1.72/0.99  inst_num_moves_active_passive:          18
% 1.72/0.99  inst_lit_activity:                      0
% 1.72/0.99  inst_lit_activity_moves:                0
% 1.72/0.99  inst_num_tautologies:                   0
% 1.72/0.99  inst_num_prop_implied:                  0
% 1.72/0.99  inst_num_existing_simplified:           0
% 1.72/0.99  inst_num_eq_res_simplified:             0
% 1.72/0.99  inst_num_child_elim:                    0
% 1.72/0.99  inst_num_of_dismatching_blockings:      20
% 1.72/0.99  inst_num_of_non_proper_insts:           207
% 1.72/0.99  inst_num_of_duplicates:                 0
% 1.72/0.99  inst_inst_num_from_inst_to_res:         0
% 1.72/0.99  inst_dismatching_checking_time:         0.
% 1.72/0.99  
% 1.72/0.99  ------ Resolution
% 1.72/0.99  
% 1.72/0.99  res_num_of_clauses:                     0
% 1.72/0.99  res_num_in_passive:                     0
% 1.72/0.99  res_num_in_active:                      0
% 1.72/0.99  res_num_of_loops:                       131
% 1.72/0.99  res_forward_subset_subsumed:            56
% 1.72/0.99  res_backward_subset_subsumed:           0
% 1.72/0.99  res_forward_subsumed:                   0
% 1.72/0.99  res_backward_subsumed:                  0
% 1.72/0.99  res_forward_subsumption_resolution:     6
% 1.72/0.99  res_backward_subsumption_resolution:    0
% 1.72/0.99  res_clause_to_clause_subsumption:       167
% 1.72/0.99  res_orphan_elimination:                 0
% 1.72/0.99  res_tautology_del:                      64
% 1.72/0.99  res_num_eq_res_simplified:              0
% 1.72/0.99  res_num_sel_changes:                    0
% 1.72/0.99  res_moves_from_active_to_pass:          0
% 1.72/0.99  
% 1.72/0.99  ------ Superposition
% 1.72/0.99  
% 1.72/0.99  sup_time_total:                         0.
% 1.72/0.99  sup_time_generating:                    0.
% 1.72/0.99  sup_time_sim_full:                      0.
% 1.72/0.99  sup_time_sim_immed:                     0.
% 1.72/0.99  
% 1.72/0.99  sup_num_of_clauses:                     38
% 1.72/0.99  sup_num_in_active:                      36
% 1.72/0.99  sup_num_in_passive:                     2
% 1.72/0.99  sup_num_of_loops:                       36
% 1.72/0.99  sup_fw_superposition:                   9
% 1.72/0.99  sup_bw_superposition:                   3
% 1.72/0.99  sup_immediate_simplified:               2
% 1.72/0.99  sup_given_eliminated:                   0
% 1.72/0.99  comparisons_done:                       0
% 1.72/0.99  comparisons_avoided:                    0
% 1.72/0.99  
% 1.72/0.99  ------ Simplifications
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  sim_fw_subset_subsumed:                 0
% 1.72/0.99  sim_bw_subset_subsumed:                 1
% 1.72/0.99  sim_fw_subsumed:                        0
% 1.72/0.99  sim_bw_subsumed:                        0
% 1.72/0.99  sim_fw_subsumption_res:                 0
% 1.72/0.99  sim_bw_subsumption_res:                 0
% 1.72/0.99  sim_tautology_del:                      1
% 1.72/0.99  sim_eq_tautology_del:                   0
% 1.72/0.99  sim_eq_res_simp:                        2
% 1.72/0.99  sim_fw_demodulated:                     0
% 1.72/0.99  sim_bw_demodulated:                     0
% 1.72/0.99  sim_light_normalised:                   7
% 1.72/0.99  sim_joinable_taut:                      0
% 1.72/0.99  sim_joinable_simp:                      0
% 1.72/0.99  sim_ac_normalised:                      0
% 1.72/0.99  sim_smt_subsumption:                    0
% 1.72/0.99  
%------------------------------------------------------------------------------
