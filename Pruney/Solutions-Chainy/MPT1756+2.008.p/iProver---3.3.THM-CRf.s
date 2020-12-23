%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:38 EST 2020

% Result     : Theorem 1.30s
% Output     : CNFRefutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 940 expanded)
%              Number of clauses        :   94 ( 134 expanded)
%              Number of leaves         :   11 ( 421 expanded)
%              Depth                    :   34
%              Number of atoms          : 1205 (19057 expanded)
%              Number of equality atoms :  160 (1248 expanded)
%              Maximal formula depth    :   27 (   9 average)
%              Maximal clause size      :   44 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

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
    inference(flattening,[],[f8])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f12])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f24,plain,(
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

fof(f23,plain,(
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

fof(f22,plain,(
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

fof(f21,plain,(
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

fof(f20,plain,(
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

fof(f19,plain,(
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

fof(f18,plain,
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

fof(f25,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f17,f24,f23,f22,f21,f20,f19,f18])).

fof(f47,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(ennf_transformation,[],[f3])).

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
    inference(flattening,[],[f10])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f30,plain,(
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
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
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
    inference(equality_resolution,[],[f30])).

fof(f48,plain,(
    r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
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
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
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
    inference(equality_resolution,[],[f31])).

fof(f51,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f46,plain,(
    v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_351,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != sK4
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_352,plain,
    ( m1_connsp_2(X0,X1,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK5,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != sK4 ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
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
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_386,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
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
    | u1_struct_0(X4) != u1_struct_0(sK3)
    | sK4 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_9])).

cnf(c_387,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(sK4,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X4) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_556,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(sK4,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X4) != u1_struct_0(sK3)
    | sK1 != X0
    | sK3 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_387,c_15])).

cnf(c_557,plain,
    ( ~ r1_tmap_1(sK1,X0,X1,X2)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
    | ~ m1_connsp_2(sK4,sK1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_561,plain,
    ( ~ l1_pre_topc(X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_connsp_2(sK4,sK1,X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ r1_tmap_1(sK1,X0,X1,X2)
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_557,c_22,c_21,c_20,c_16,c_14])).

cnf(c_562,plain,
    ( ~ r1_tmap_1(sK1,X0,X1,X2)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
    | ~ m1_connsp_2(sK4,sK1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_561])).

cnf(c_606,plain,
    ( ~ r1_tmap_1(sK1,X0,X1,X2)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ m1_connsp_2(sK4,sK1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_562])).

cnf(c_607,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_connsp_2(sK4,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ v1_funct_1(sK2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_611,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_connsp_2(sK4,sK1,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ r1_tmap_1(sK1,X0,sK2,X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_607,c_19])).

cnf(c_612,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_connsp_2(sK4,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_611])).

cnf(c_751,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(X3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X3,X2) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | sK4 != X2
    | sK5 != X1
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_352,c_612])).

cnf(c_752,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,sK5)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,sK4) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_751])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_756,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,X0,sK2,sK5)
    | ~ v2_pre_topc(X0)
    | k1_tops_1(sK1,sK4) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_752,c_22,c_21,c_20,c_14,c_13])).

cnf(c_757,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,sK5)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k1_tops_1(sK1,sK4) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_756])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_898,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,sK5)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | k1_tops_1(sK1,sK4) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_757,c_23])).

cnf(c_899,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | k1_tops_1(sK1,sK4) != sK4
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_898])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_901,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | k1_tops_1(sK1,sK4) != sK4
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_899,c_25,c_24,c_17])).

cnf(c_902,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | k1_tops_1(sK1,sK4) != sK4
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_901])).

cnf(c_990,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | k1_tops_1(sK1,sK4) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_902])).

cnf(c_1092,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | k1_tops_1(sK1,sK4) != sK4 ),
    inference(subtyping,[status(esa)],[c_990])).

cnf(c_1441,plain,
    ( k1_tops_1(sK1,sK4) != sK4
    | r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1092])).

cnf(c_8,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1102,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1479,plain,
    ( k1_tops_1(sK1,sK4) != sK4
    | r1_tmap_1(sK1,sK0,sK2,sK6) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1441,c_1102])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1101,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1432,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1101])).

cnf(c_4,plain,
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
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_446,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
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
    | u1_struct_0(X4) != u1_struct_0(sK3)
    | sK4 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_9])).

cnf(c_447,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(sK4,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X4) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_508,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(sK4,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X4) != u1_struct_0(sK3)
    | sK1 != X0
    | sK3 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_447,c_15])).

cnf(c_509,plain,
    ( r1_tmap_1(sK1,X0,X1,X2)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
    | ~ m1_connsp_2(sK4,sK1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_513,plain,
    ( ~ l1_pre_topc(X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_connsp_2(sK4,sK1,X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | r1_tmap_1(sK1,X0,X1,X2)
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_509,c_22,c_21,c_20,c_16,c_14])).

cnf(c_514,plain,
    ( r1_tmap_1(sK1,X0,X1,X2)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
    | ~ m1_connsp_2(sK4,sK1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_513])).

cnf(c_648,plain,
    ( r1_tmap_1(sK1,X0,X1,X2)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ m1_connsp_2(sK4,sK1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_514])).

cnf(c_649,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_connsp_2(sK4,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ v1_funct_1(sK2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_653,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_connsp_2(sK4,sK1,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | r1_tmap_1(sK1,X0,sK2,X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_649,c_19])).

cnf(c_654,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_connsp_2(sK4,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_653])).

cnf(c_712,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(X3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X3,X2) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | sK4 != X2
    | sK5 != X1
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_352,c_654])).

cnf(c_713,plain,
    ( r1_tmap_1(sK1,X0,sK2,sK5)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,sK4) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_712])).

cnf(c_717,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,X0,sK2,sK5)
    | ~ v2_pre_topc(X0)
    | k1_tops_1(sK1,sK4) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_713,c_22,c_21,c_20,c_14,c_13])).

cnf(c_718,plain,
    ( r1_tmap_1(sK1,X0,sK2,sK5)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k1_tops_1(sK1,sK4) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_717])).

cnf(c_921,plain,
    ( r1_tmap_1(sK1,X0,sK2,sK5)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | k1_tops_1(sK1,sK4) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_718,c_23])).

cnf(c_922,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | k1_tops_1(sK1,sK4) != sK4
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_921])).

cnf(c_924,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK5)
    | k1_tops_1(sK1,sK4) != sK4
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_922,c_25,c_24,c_17])).

cnf(c_925,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | k1_tops_1(sK1,sK4) != sK4
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_924])).

cnf(c_988,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | k1_tops_1(sK1,sK4) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_925])).

cnf(c_1093,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | k1_tops_1(sK1,sK4) != sK4 ),
    inference(subtyping,[status(esa)],[c_988])).

cnf(c_1440,plain,
    ( k1_tops_1(sK1,sK4) != sK4
    | r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1093])).

cnf(c_1471,plain,
    ( k1_tops_1(sK1,sK4) != sK4
    | r1_tmap_1(sK1,sK0,sK2,sK6) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1440,c_1102])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1104,negated_conjecture,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1430,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1104])).

cnf(c_1466,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK6) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1430,c_1102])).

cnf(c_1476,plain,
    ( k1_tops_1(sK1,sK4) != sK4
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1471,c_1432,c_1466])).

cnf(c_7,negated_conjecture,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1103,negated_conjecture,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1431,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1103])).

cnf(c_1461,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK6) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1431,c_1102])).

cnf(c_1484,plain,
    ( k1_tops_1(sK1,sK4) != sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1479,c_1432,c_1476,c_1461])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X0,X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_11,negated_conjecture,
    ( v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X3,X2) = X2
    | sK4 != X2
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_322,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,sK4) = sK4 ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_326,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(sK1,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_322,c_20,c_14])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(sK1,sK4) = sK4 ),
    inference(renaming,[status(thm)],[c_326])).

cnf(c_810,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | k1_tops_1(sK1,sK4) = sK4
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_327,c_20])).

cnf(c_811,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | k1_tops_1(sK1,sK4) = sK4 ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_815,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_811,c_21])).

cnf(c_1097,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,sK4) = sK4 ),
    inference(subtyping,[status(esa)],[c_815])).

cnf(c_1436,plain,
    ( k1_tops_1(sK1,sK4) = sK4
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1097])).

cnf(c_1486,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1484,c_1436])).

cnf(c_1099,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1434,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1099])).

cnf(c_1492,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1486,c_1434])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:12:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.30/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.30/0.99  
% 1.30/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.30/0.99  
% 1.30/0.99  ------  iProver source info
% 1.30/0.99  
% 1.30/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.30/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.30/0.99  git: non_committed_changes: false
% 1.30/0.99  git: last_make_outside_of_git: false
% 1.30/0.99  
% 1.30/0.99  ------ 
% 1.30/0.99  
% 1.30/0.99  ------ Input Options
% 1.30/0.99  
% 1.30/0.99  --out_options                           all
% 1.30/0.99  --tptp_safe_out                         true
% 1.30/0.99  --problem_path                          ""
% 1.30/0.99  --include_path                          ""
% 1.30/0.99  --clausifier                            res/vclausify_rel
% 1.30/0.99  --clausifier_options                    --mode clausify
% 1.30/0.99  --stdin                                 false
% 1.30/0.99  --stats_out                             all
% 1.30/0.99  
% 1.30/0.99  ------ General Options
% 1.30/0.99  
% 1.30/0.99  --fof                                   false
% 1.30/0.99  --time_out_real                         305.
% 1.30/0.99  --time_out_virtual                      -1.
% 1.30/0.99  --symbol_type_check                     false
% 1.30/0.99  --clausify_out                          false
% 1.30/0.99  --sig_cnt_out                           false
% 1.30/0.99  --trig_cnt_out                          false
% 1.30/0.99  --trig_cnt_out_tolerance                1.
% 1.30/0.99  --trig_cnt_out_sk_spl                   false
% 1.30/0.99  --abstr_cl_out                          false
% 1.30/0.99  
% 1.30/0.99  ------ Global Options
% 1.30/0.99  
% 1.30/0.99  --schedule                              default
% 1.30/0.99  --add_important_lit                     false
% 1.30/0.99  --prop_solver_per_cl                    1000
% 1.30/0.99  --min_unsat_core                        false
% 1.30/0.99  --soft_assumptions                      false
% 1.30/0.99  --soft_lemma_size                       3
% 1.30/0.99  --prop_impl_unit_size                   0
% 1.30/0.99  --prop_impl_unit                        []
% 1.30/0.99  --share_sel_clauses                     true
% 1.30/0.99  --reset_solvers                         false
% 1.30/0.99  --bc_imp_inh                            [conj_cone]
% 1.30/0.99  --conj_cone_tolerance                   3.
% 1.30/0.99  --extra_neg_conj                        none
% 1.30/0.99  --large_theory_mode                     true
% 1.30/0.99  --prolific_symb_bound                   200
% 1.30/0.99  --lt_threshold                          2000
% 1.30/0.99  --clause_weak_htbl                      true
% 1.30/0.99  --gc_record_bc_elim                     false
% 1.30/0.99  
% 1.30/0.99  ------ Preprocessing Options
% 1.30/0.99  
% 1.30/0.99  --preprocessing_flag                    true
% 1.30/0.99  --time_out_prep_mult                    0.1
% 1.30/0.99  --splitting_mode                        input
% 1.30/0.99  --splitting_grd                         true
% 1.30/0.99  --splitting_cvd                         false
% 1.30/0.99  --splitting_cvd_svl                     false
% 1.30/0.99  --splitting_nvd                         32
% 1.30/0.99  --sub_typing                            true
% 1.30/0.99  --prep_gs_sim                           true
% 1.30/0.99  --prep_unflatten                        true
% 1.30/0.99  --prep_res_sim                          true
% 1.30/0.99  --prep_upred                            true
% 1.30/0.99  --prep_sem_filter                       exhaustive
% 1.30/0.99  --prep_sem_filter_out                   false
% 1.30/0.99  --pred_elim                             true
% 1.30/0.99  --res_sim_input                         true
% 1.30/0.99  --eq_ax_congr_red                       true
% 1.30/0.99  --pure_diseq_elim                       true
% 1.30/0.99  --brand_transform                       false
% 1.30/0.99  --non_eq_to_eq                          false
% 1.30/0.99  --prep_def_merge                        true
% 1.30/0.99  --prep_def_merge_prop_impl              false
% 1.30/0.99  --prep_def_merge_mbd                    true
% 1.30/0.99  --prep_def_merge_tr_red                 false
% 1.30/0.99  --prep_def_merge_tr_cl                  false
% 1.30/0.99  --smt_preprocessing                     true
% 1.30/0.99  --smt_ac_axioms                         fast
% 1.30/0.99  --preprocessed_out                      false
% 1.30/0.99  --preprocessed_stats                    false
% 1.30/0.99  
% 1.30/0.99  ------ Abstraction refinement Options
% 1.30/0.99  
% 1.30/0.99  --abstr_ref                             []
% 1.30/0.99  --abstr_ref_prep                        false
% 1.30/0.99  --abstr_ref_until_sat                   false
% 1.30/0.99  --abstr_ref_sig_restrict                funpre
% 1.30/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.30/0.99  --abstr_ref_under                       []
% 1.30/0.99  
% 1.30/0.99  ------ SAT Options
% 1.30/0.99  
% 1.30/0.99  --sat_mode                              false
% 1.30/0.99  --sat_fm_restart_options                ""
% 1.30/0.99  --sat_gr_def                            false
% 1.30/0.99  --sat_epr_types                         true
% 1.30/0.99  --sat_non_cyclic_types                  false
% 1.30/0.99  --sat_finite_models                     false
% 1.30/0.99  --sat_fm_lemmas                         false
% 1.30/0.99  --sat_fm_prep                           false
% 1.30/0.99  --sat_fm_uc_incr                        true
% 1.30/0.99  --sat_out_model                         small
% 1.30/0.99  --sat_out_clauses                       false
% 1.30/0.99  
% 1.30/0.99  ------ QBF Options
% 1.30/0.99  
% 1.30/0.99  --qbf_mode                              false
% 1.30/0.99  --qbf_elim_univ                         false
% 1.30/0.99  --qbf_dom_inst                          none
% 1.30/0.99  --qbf_dom_pre_inst                      false
% 1.30/0.99  --qbf_sk_in                             false
% 1.30/0.99  --qbf_pred_elim                         true
% 1.30/0.99  --qbf_split                             512
% 1.30/0.99  
% 1.30/0.99  ------ BMC1 Options
% 1.30/0.99  
% 1.30/0.99  --bmc1_incremental                      false
% 1.30/0.99  --bmc1_axioms                           reachable_all
% 1.30/0.99  --bmc1_min_bound                        0
% 1.30/0.99  --bmc1_max_bound                        -1
% 1.30/0.99  --bmc1_max_bound_default                -1
% 1.30/0.99  --bmc1_symbol_reachability              true
% 1.30/0.99  --bmc1_property_lemmas                  false
% 1.30/0.99  --bmc1_k_induction                      false
% 1.30/0.99  --bmc1_non_equiv_states                 false
% 1.30/0.99  --bmc1_deadlock                         false
% 1.30/0.99  --bmc1_ucm                              false
% 1.30/0.99  --bmc1_add_unsat_core                   none
% 1.30/0.99  --bmc1_unsat_core_children              false
% 1.30/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.30/0.99  --bmc1_out_stat                         full
% 1.30/0.99  --bmc1_ground_init                      false
% 1.30/0.99  --bmc1_pre_inst_next_state              false
% 1.30/0.99  --bmc1_pre_inst_state                   false
% 1.30/0.99  --bmc1_pre_inst_reach_state             false
% 1.30/0.99  --bmc1_out_unsat_core                   false
% 1.30/0.99  --bmc1_aig_witness_out                  false
% 1.30/0.99  --bmc1_verbose                          false
% 1.30/0.99  --bmc1_dump_clauses_tptp                false
% 1.30/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.30/0.99  --bmc1_dump_file                        -
% 1.30/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.30/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.30/0.99  --bmc1_ucm_extend_mode                  1
% 1.30/0.99  --bmc1_ucm_init_mode                    2
% 1.30/0.99  --bmc1_ucm_cone_mode                    none
% 1.30/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.30/0.99  --bmc1_ucm_relax_model                  4
% 1.30/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.30/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.30/0.99  --bmc1_ucm_layered_model                none
% 1.30/0.99  --bmc1_ucm_max_lemma_size               10
% 1.30/0.99  
% 1.30/0.99  ------ AIG Options
% 1.30/0.99  
% 1.30/0.99  --aig_mode                              false
% 1.30/0.99  
% 1.30/0.99  ------ Instantiation Options
% 1.30/0.99  
% 1.30/0.99  --instantiation_flag                    true
% 1.30/0.99  --inst_sos_flag                         false
% 1.30/0.99  --inst_sos_phase                        true
% 1.30/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.30/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.30/0.99  --inst_lit_sel_side                     num_symb
% 1.30/0.99  --inst_solver_per_active                1400
% 1.30/0.99  --inst_solver_calls_frac                1.
% 1.30/0.99  --inst_passive_queue_type               priority_queues
% 1.30/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.30/0.99  --inst_passive_queues_freq              [25;2]
% 1.30/0.99  --inst_dismatching                      true
% 1.30/0.99  --inst_eager_unprocessed_to_passive     true
% 1.30/0.99  --inst_prop_sim_given                   true
% 1.30/0.99  --inst_prop_sim_new                     false
% 1.30/0.99  --inst_subs_new                         false
% 1.30/0.99  --inst_eq_res_simp                      false
% 1.30/0.99  --inst_subs_given                       false
% 1.30/0.99  --inst_orphan_elimination               true
% 1.30/0.99  --inst_learning_loop_flag               true
% 1.30/0.99  --inst_learning_start                   3000
% 1.30/0.99  --inst_learning_factor                  2
% 1.30/0.99  --inst_start_prop_sim_after_learn       3
% 1.30/0.99  --inst_sel_renew                        solver
% 1.30/0.99  --inst_lit_activity_flag                true
% 1.30/0.99  --inst_restr_to_given                   false
% 1.30/0.99  --inst_activity_threshold               500
% 1.30/0.99  --inst_out_proof                        true
% 1.30/0.99  
% 1.30/0.99  ------ Resolution Options
% 1.30/0.99  
% 1.30/0.99  --resolution_flag                       true
% 1.30/0.99  --res_lit_sel                           adaptive
% 1.30/0.99  --res_lit_sel_side                      none
% 1.30/0.99  --res_ordering                          kbo
% 1.30/0.99  --res_to_prop_solver                    active
% 1.30/0.99  --res_prop_simpl_new                    false
% 1.30/0.99  --res_prop_simpl_given                  true
% 1.30/0.99  --res_passive_queue_type                priority_queues
% 1.30/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.30/0.99  --res_passive_queues_freq               [15;5]
% 1.30/0.99  --res_forward_subs                      full
% 1.30/0.99  --res_backward_subs                     full
% 1.30/0.99  --res_forward_subs_resolution           true
% 1.30/0.99  --res_backward_subs_resolution          true
% 1.30/0.99  --res_orphan_elimination                true
% 1.30/0.99  --res_time_limit                        2.
% 1.30/0.99  --res_out_proof                         true
% 1.30/0.99  
% 1.30/0.99  ------ Superposition Options
% 1.30/0.99  
% 1.30/0.99  --superposition_flag                    true
% 1.30/0.99  --sup_passive_queue_type                priority_queues
% 1.30/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.30/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.30/0.99  --demod_completeness_check              fast
% 1.30/0.99  --demod_use_ground                      true
% 1.30/0.99  --sup_to_prop_solver                    passive
% 1.30/0.99  --sup_prop_simpl_new                    true
% 1.30/0.99  --sup_prop_simpl_given                  true
% 1.30/0.99  --sup_fun_splitting                     false
% 1.30/0.99  --sup_smt_interval                      50000
% 1.30/0.99  
% 1.30/0.99  ------ Superposition Simplification Setup
% 1.30/0.99  
% 1.30/0.99  --sup_indices_passive                   []
% 1.30/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.30/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/0.99  --sup_full_bw                           [BwDemod]
% 1.30/0.99  --sup_immed_triv                        [TrivRules]
% 1.30/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.30/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/0.99  --sup_immed_bw_main                     []
% 1.30/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.30/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.30/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.30/0.99  
% 1.30/0.99  ------ Combination Options
% 1.30/0.99  
% 1.30/0.99  --comb_res_mult                         3
% 1.30/0.99  --comb_sup_mult                         2
% 1.30/0.99  --comb_inst_mult                        10
% 1.30/0.99  
% 1.30/0.99  ------ Debug Options
% 1.30/0.99  
% 1.30/0.99  --dbg_backtrace                         false
% 1.30/0.99  --dbg_dump_prop_clauses                 false
% 1.30/0.99  --dbg_dump_prop_clauses_file            -
% 1.30/0.99  --dbg_out_stat                          false
% 1.30/0.99  ------ Parsing...
% 1.30/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.30/0.99  
% 1.30/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 1.30/0.99  
% 1.30/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.30/0.99  
% 1.30/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.30/0.99  ------ Proving...
% 1.30/0.99  ------ Problem Properties 
% 1.30/0.99  
% 1.30/0.99  
% 1.30/0.99  clauses                                 13
% 1.30/0.99  conjectures                             7
% 1.30/0.99  EPR                                     1
% 1.30/0.99  Horn                                    12
% 1.30/0.99  unary                                   5
% 1.30/0.99  binary                                  4
% 1.30/0.99  lits                                    33
% 1.30/0.99  lits eq                                 9
% 1.30/0.99  fd_pure                                 0
% 1.30/0.99  fd_pseudo                               0
% 1.30/0.99  fd_cond                                 0
% 1.30/0.99  fd_pseudo_cond                          0
% 1.30/0.99  AC symbols                              0
% 1.30/0.99  
% 1.30/0.99  ------ Schedule dynamic 5 is on 
% 1.30/0.99  
% 1.30/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.30/0.99  
% 1.30/0.99  
% 1.30/0.99  ------ 
% 1.30/0.99  Current options:
% 1.30/0.99  ------ 
% 1.30/0.99  
% 1.30/0.99  ------ Input Options
% 1.30/0.99  
% 1.30/0.99  --out_options                           all
% 1.30/0.99  --tptp_safe_out                         true
% 1.30/0.99  --problem_path                          ""
% 1.30/0.99  --include_path                          ""
% 1.30/0.99  --clausifier                            res/vclausify_rel
% 1.30/0.99  --clausifier_options                    --mode clausify
% 1.30/0.99  --stdin                                 false
% 1.30/0.99  --stats_out                             all
% 1.30/0.99  
% 1.30/0.99  ------ General Options
% 1.30/0.99  
% 1.30/0.99  --fof                                   false
% 1.30/0.99  --time_out_real                         305.
% 1.30/0.99  --time_out_virtual                      -1.
% 1.30/0.99  --symbol_type_check                     false
% 1.30/0.99  --clausify_out                          false
% 1.30/0.99  --sig_cnt_out                           false
% 1.30/0.99  --trig_cnt_out                          false
% 1.30/0.99  --trig_cnt_out_tolerance                1.
% 1.30/0.99  --trig_cnt_out_sk_spl                   false
% 1.30/0.99  --abstr_cl_out                          false
% 1.30/0.99  
% 1.30/0.99  ------ Global Options
% 1.30/0.99  
% 1.30/0.99  --schedule                              default
% 1.30/0.99  --add_important_lit                     false
% 1.30/0.99  --prop_solver_per_cl                    1000
% 1.30/0.99  --min_unsat_core                        false
% 1.30/0.99  --soft_assumptions                      false
% 1.30/0.99  --soft_lemma_size                       3
% 1.30/0.99  --prop_impl_unit_size                   0
% 1.30/0.99  --prop_impl_unit                        []
% 1.30/0.99  --share_sel_clauses                     true
% 1.30/0.99  --reset_solvers                         false
% 1.30/0.99  --bc_imp_inh                            [conj_cone]
% 1.30/0.99  --conj_cone_tolerance                   3.
% 1.30/0.99  --extra_neg_conj                        none
% 1.30/0.99  --large_theory_mode                     true
% 1.30/0.99  --prolific_symb_bound                   200
% 1.30/0.99  --lt_threshold                          2000
% 1.30/0.99  --clause_weak_htbl                      true
% 1.30/0.99  --gc_record_bc_elim                     false
% 1.30/0.99  
% 1.30/0.99  ------ Preprocessing Options
% 1.30/0.99  
% 1.30/0.99  --preprocessing_flag                    true
% 1.30/0.99  --time_out_prep_mult                    0.1
% 1.30/0.99  --splitting_mode                        input
% 1.30/0.99  --splitting_grd                         true
% 1.30/0.99  --splitting_cvd                         false
% 1.30/0.99  --splitting_cvd_svl                     false
% 1.30/0.99  --splitting_nvd                         32
% 1.30/0.99  --sub_typing                            true
% 1.30/0.99  --prep_gs_sim                           true
% 1.30/0.99  --prep_unflatten                        true
% 1.30/0.99  --prep_res_sim                          true
% 1.30/0.99  --prep_upred                            true
% 1.30/0.99  --prep_sem_filter                       exhaustive
% 1.30/0.99  --prep_sem_filter_out                   false
% 1.30/0.99  --pred_elim                             true
% 1.30/0.99  --res_sim_input                         true
% 1.30/0.99  --eq_ax_congr_red                       true
% 1.30/0.99  --pure_diseq_elim                       true
% 1.30/0.99  --brand_transform                       false
% 1.30/0.99  --non_eq_to_eq                          false
% 1.30/0.99  --prep_def_merge                        true
% 1.30/0.99  --prep_def_merge_prop_impl              false
% 1.30/0.99  --prep_def_merge_mbd                    true
% 1.30/0.99  --prep_def_merge_tr_red                 false
% 1.30/0.99  --prep_def_merge_tr_cl                  false
% 1.30/0.99  --smt_preprocessing                     true
% 1.30/0.99  --smt_ac_axioms                         fast
% 1.30/0.99  --preprocessed_out                      false
% 1.30/0.99  --preprocessed_stats                    false
% 1.30/0.99  
% 1.30/0.99  ------ Abstraction refinement Options
% 1.30/0.99  
% 1.30/0.99  --abstr_ref                             []
% 1.30/0.99  --abstr_ref_prep                        false
% 1.30/0.99  --abstr_ref_until_sat                   false
% 1.30/0.99  --abstr_ref_sig_restrict                funpre
% 1.30/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.30/0.99  --abstr_ref_under                       []
% 1.30/0.99  
% 1.30/0.99  ------ SAT Options
% 1.30/0.99  
% 1.30/0.99  --sat_mode                              false
% 1.30/0.99  --sat_fm_restart_options                ""
% 1.30/0.99  --sat_gr_def                            false
% 1.30/0.99  --sat_epr_types                         true
% 1.30/0.99  --sat_non_cyclic_types                  false
% 1.30/0.99  --sat_finite_models                     false
% 1.30/0.99  --sat_fm_lemmas                         false
% 1.30/0.99  --sat_fm_prep                           false
% 1.30/0.99  --sat_fm_uc_incr                        true
% 1.30/0.99  --sat_out_model                         small
% 1.30/0.99  --sat_out_clauses                       false
% 1.30/0.99  
% 1.30/0.99  ------ QBF Options
% 1.30/0.99  
% 1.30/0.99  --qbf_mode                              false
% 1.30/0.99  --qbf_elim_univ                         false
% 1.30/0.99  --qbf_dom_inst                          none
% 1.30/0.99  --qbf_dom_pre_inst                      false
% 1.30/0.99  --qbf_sk_in                             false
% 1.30/0.99  --qbf_pred_elim                         true
% 1.30/0.99  --qbf_split                             512
% 1.30/0.99  
% 1.30/0.99  ------ BMC1 Options
% 1.30/0.99  
% 1.30/0.99  --bmc1_incremental                      false
% 1.30/0.99  --bmc1_axioms                           reachable_all
% 1.30/0.99  --bmc1_min_bound                        0
% 1.30/0.99  --bmc1_max_bound                        -1
% 1.30/0.99  --bmc1_max_bound_default                -1
% 1.30/0.99  --bmc1_symbol_reachability              true
% 1.30/0.99  --bmc1_property_lemmas                  false
% 1.30/0.99  --bmc1_k_induction                      false
% 1.30/0.99  --bmc1_non_equiv_states                 false
% 1.30/0.99  --bmc1_deadlock                         false
% 1.30/0.99  --bmc1_ucm                              false
% 1.30/0.99  --bmc1_add_unsat_core                   none
% 1.30/0.99  --bmc1_unsat_core_children              false
% 1.30/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.30/0.99  --bmc1_out_stat                         full
% 1.30/0.99  --bmc1_ground_init                      false
% 1.30/0.99  --bmc1_pre_inst_next_state              false
% 1.30/0.99  --bmc1_pre_inst_state                   false
% 1.30/0.99  --bmc1_pre_inst_reach_state             false
% 1.30/0.99  --bmc1_out_unsat_core                   false
% 1.30/0.99  --bmc1_aig_witness_out                  false
% 1.30/0.99  --bmc1_verbose                          false
% 1.30/0.99  --bmc1_dump_clauses_tptp                false
% 1.30/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.30/0.99  --bmc1_dump_file                        -
% 1.30/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.30/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.30/0.99  --bmc1_ucm_extend_mode                  1
% 1.30/0.99  --bmc1_ucm_init_mode                    2
% 1.30/0.99  --bmc1_ucm_cone_mode                    none
% 1.30/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.30/0.99  --bmc1_ucm_relax_model                  4
% 1.30/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.30/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.30/0.99  --bmc1_ucm_layered_model                none
% 1.30/0.99  --bmc1_ucm_max_lemma_size               10
% 1.30/0.99  
% 1.30/0.99  ------ AIG Options
% 1.30/0.99  
% 1.30/0.99  --aig_mode                              false
% 1.30/0.99  
% 1.30/0.99  ------ Instantiation Options
% 1.30/0.99  
% 1.30/0.99  --instantiation_flag                    true
% 1.30/0.99  --inst_sos_flag                         false
% 1.30/0.99  --inst_sos_phase                        true
% 1.30/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.30/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.30/0.99  --inst_lit_sel_side                     none
% 1.30/0.99  --inst_solver_per_active                1400
% 1.30/0.99  --inst_solver_calls_frac                1.
% 1.30/0.99  --inst_passive_queue_type               priority_queues
% 1.30/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.30/0.99  --inst_passive_queues_freq              [25;2]
% 1.30/0.99  --inst_dismatching                      true
% 1.30/0.99  --inst_eager_unprocessed_to_passive     true
% 1.30/0.99  --inst_prop_sim_given                   true
% 1.30/0.99  --inst_prop_sim_new                     false
% 1.30/0.99  --inst_subs_new                         false
% 1.30/0.99  --inst_eq_res_simp                      false
% 1.30/0.99  --inst_subs_given                       false
% 1.30/0.99  --inst_orphan_elimination               true
% 1.30/0.99  --inst_learning_loop_flag               true
% 1.30/0.99  --inst_learning_start                   3000
% 1.30/0.99  --inst_learning_factor                  2
% 1.30/0.99  --inst_start_prop_sim_after_learn       3
% 1.30/0.99  --inst_sel_renew                        solver
% 1.30/0.99  --inst_lit_activity_flag                true
% 1.30/0.99  --inst_restr_to_given                   false
% 1.30/0.99  --inst_activity_threshold               500
% 1.30/0.99  --inst_out_proof                        true
% 1.30/0.99  
% 1.30/0.99  ------ Resolution Options
% 1.30/0.99  
% 1.30/0.99  --resolution_flag                       false
% 1.30/0.99  --res_lit_sel                           adaptive
% 1.30/0.99  --res_lit_sel_side                      none
% 1.30/0.99  --res_ordering                          kbo
% 1.30/0.99  --res_to_prop_solver                    active
% 1.30/0.99  --res_prop_simpl_new                    false
% 1.30/0.99  --res_prop_simpl_given                  true
% 1.30/0.99  --res_passive_queue_type                priority_queues
% 1.30/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.30/0.99  --res_passive_queues_freq               [15;5]
% 1.30/0.99  --res_forward_subs                      full
% 1.30/0.99  --res_backward_subs                     full
% 1.30/0.99  --res_forward_subs_resolution           true
% 1.30/0.99  --res_backward_subs_resolution          true
% 1.30/0.99  --res_orphan_elimination                true
% 1.30/0.99  --res_time_limit                        2.
% 1.30/0.99  --res_out_proof                         true
% 1.30/0.99  
% 1.30/0.99  ------ Superposition Options
% 1.30/0.99  
% 1.30/0.99  --superposition_flag                    true
% 1.30/0.99  --sup_passive_queue_type                priority_queues
% 1.30/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.30/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.30/0.99  --demod_completeness_check              fast
% 1.30/0.99  --demod_use_ground                      true
% 1.30/0.99  --sup_to_prop_solver                    passive
% 1.30/0.99  --sup_prop_simpl_new                    true
% 1.30/0.99  --sup_prop_simpl_given                  true
% 1.30/0.99  --sup_fun_splitting                     false
% 1.30/0.99  --sup_smt_interval                      50000
% 1.30/0.99  
% 1.30/0.99  ------ Superposition Simplification Setup
% 1.30/0.99  
% 1.30/0.99  --sup_indices_passive                   []
% 1.30/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.30/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/0.99  --sup_full_bw                           [BwDemod]
% 1.30/0.99  --sup_immed_triv                        [TrivRules]
% 1.30/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.30/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/0.99  --sup_immed_bw_main                     []
% 1.30/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.30/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.30/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.30/0.99  
% 1.30/0.99  ------ Combination Options
% 1.30/0.99  
% 1.30/0.99  --comb_res_mult                         3
% 1.30/0.99  --comb_sup_mult                         2
% 1.30/0.99  --comb_inst_mult                        10
% 1.30/0.99  
% 1.30/0.99  ------ Debug Options
% 1.30/0.99  
% 1.30/0.99  --dbg_backtrace                         false
% 1.30/0.99  --dbg_dump_prop_clauses                 false
% 1.30/0.99  --dbg_dump_prop_clauses_file            -
% 1.30/0.99  --dbg_out_stat                          false
% 1.30/0.99  
% 1.30/0.99  
% 1.30/0.99  
% 1.30/0.99  
% 1.30/0.99  ------ Proving...
% 1.30/0.99  
% 1.30/0.99  
% 1.30/0.99  % SZS status Theorem for theBenchmark.p
% 1.30/0.99  
% 1.30/0.99   Resolution empty clause
% 1.30/0.99  
% 1.30/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.30/0.99  
% 1.30/0.99  fof(f2,axiom,(
% 1.30/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/0.99  
% 1.30/0.99  fof(f8,plain,(
% 1.30/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.30/0.99    inference(ennf_transformation,[],[f2])).
% 1.30/0.99  
% 1.30/0.99  fof(f9,plain,(
% 1.30/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.99    inference(flattening,[],[f8])).
% 1.30/0.99  
% 1.30/0.99  fof(f14,plain,(
% 1.30/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.99    inference(nnf_transformation,[],[f9])).
% 1.30/0.99  
% 1.30/0.99  fof(f29,plain,(
% 1.30/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.99    inference(cnf_transformation,[],[f14])).
% 1.30/0.99  
% 1.30/0.99  fof(f4,conjecture,(
% 1.30/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/0.99  
% 1.30/0.99  fof(f5,negated_conjecture,(
% 1.30/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.30/0.99    inference(negated_conjecture,[],[f4])).
% 1.30/0.99  
% 1.30/0.99  fof(f12,plain,(
% 1.30/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.30/0.99    inference(ennf_transformation,[],[f5])).
% 1.30/0.99  
% 1.30/0.99  fof(f13,plain,(
% 1.30/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.30/0.99    inference(flattening,[],[f12])).
% 1.30/0.99  
% 1.30/0.99  fof(f16,plain,(
% 1.30/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5))) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.30/0.99    inference(nnf_transformation,[],[f13])).
% 1.30/0.99  
% 1.30/0.99  fof(f17,plain,(
% 1.30/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.30/0.99    inference(flattening,[],[f16])).
% 1.30/0.99  
% 1.30/0.99  fof(f24,plain,(
% 1.30/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | r1_tmap_1(X1,X0,X2,X5)) & sK6 = X5 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 1.30/0.99    introduced(choice_axiom,[])).
% 1.30/0.99  
% 1.30/0.99  fof(f23,plain,(
% 1.30/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,sK5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,sK5)) & sK5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(sK5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,u1_struct_0(X1)))) )),
% 1.30/0.99    introduced(choice_axiom,[])).
% 1.30/0.99  
% 1.30/0.99  fof(f22,plain,(
% 1.30/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(sK4,u1_struct_0(X3)) & r2_hidden(X5,sK4) & v3_pre_topc(sK4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 1.30/0.99    introduced(choice_axiom,[])).
% 1.30/0.99  
% 1.30/0.99  fof(f21,plain,(
% 1.30/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(sK3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 1.30/0.99    introduced(choice_axiom,[])).
% 1.30/0.99  
% 1.30/0.99  fof(f20,plain,(
% 1.30/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X6) | ~r1_tmap_1(X1,X0,sK2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X6) | r1_tmap_1(X1,X0,sK2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK2))) )),
% 1.30/0.99    introduced(choice_axiom,[])).
% 1.30/0.99  
% 1.30/0.99  fof(f19,plain,(
% 1.30/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X6) | ~r1_tmap_1(sK1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X6) | r1_tmap_1(sK1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.30/0.99    introduced(choice_axiom,[])).
% 1.30/0.99  
% 1.30/0.99  fof(f18,plain,(
% 1.30/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6) | ~r1_tmap_1(X1,sK0,X2,X5)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6) | r1_tmap_1(X1,sK0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.30/0.99    introduced(choice_axiom,[])).
% 1.30/0.99  
% 1.30/0.99  fof(f25,plain,(
% 1.30/0.99    (((((((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)) & sK5 = sK6 & r1_tarski(sK4,u1_struct_0(sK3)) & r2_hidden(sK5,sK4) & v3_pre_topc(sK4,sK1) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.30/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f17,f24,f23,f22,f21,f20,f19,f18])).
% 1.30/0.99  
% 1.30/0.99  fof(f47,plain,(
% 1.30/0.99    r2_hidden(sK5,sK4)),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f39,plain,(
% 1.30/0.99    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f3,axiom,(
% 1.30/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/0.99  
% 1.30/0.99  fof(f10,plain,(
% 1.30/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.30/0.99    inference(ennf_transformation,[],[f3])).
% 1.30/0.99  
% 1.30/0.99  fof(f11,plain,(
% 1.30/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.99    inference(flattening,[],[f10])).
% 1.30/0.99  
% 1.30/0.99  fof(f15,plain,(
% 1.30/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.30/0.99    inference(nnf_transformation,[],[f11])).
% 1.30/0.99  
% 1.30/0.99  fof(f30,plain,(
% 1.30/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.99    inference(cnf_transformation,[],[f15])).
% 1.30/0.99  
% 1.30/0.99  fof(f53,plain,(
% 1.30/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.99    inference(equality_resolution,[],[f30])).
% 1.30/0.99  
% 1.30/0.99  fof(f48,plain,(
% 1.30/0.99    r1_tarski(sK4,u1_struct_0(sK3))),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f42,plain,(
% 1.30/0.99    m1_pre_topc(sK3,sK1)),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f35,plain,(
% 1.30/0.99    ~v2_struct_0(sK1)),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f36,plain,(
% 1.30/0.99    v2_pre_topc(sK1)),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f37,plain,(
% 1.30/0.99    l1_pre_topc(sK1)),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f41,plain,(
% 1.30/0.99    ~v2_struct_0(sK3)),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f43,plain,(
% 1.30/0.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f38,plain,(
% 1.30/0.99    v1_funct_1(sK2)),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f44,plain,(
% 1.30/0.99    m1_subset_1(sK5,u1_struct_0(sK1))),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f34,plain,(
% 1.30/0.99    l1_pre_topc(sK0)),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f32,plain,(
% 1.30/0.99    ~v2_struct_0(sK0)),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f33,plain,(
% 1.30/0.99    v2_pre_topc(sK0)),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f40,plain,(
% 1.30/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f49,plain,(
% 1.30/0.99    sK5 = sK6),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f45,plain,(
% 1.30/0.99    m1_subset_1(sK6,u1_struct_0(sK3))),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f31,plain,(
% 1.30/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.99    inference(cnf_transformation,[],[f15])).
% 1.30/0.99  
% 1.30/0.99  fof(f52,plain,(
% 1.30/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.30/0.99    inference(equality_resolution,[],[f31])).
% 1.30/0.99  
% 1.30/0.99  fof(f51,plain,(
% 1.30/0.99    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f50,plain,(
% 1.30/0.99    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  fof(f1,axiom,(
% 1.30/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/0.99  
% 1.30/0.99  fof(f6,plain,(
% 1.30/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.30/0.99    inference(ennf_transformation,[],[f1])).
% 1.30/0.99  
% 1.30/0.99  fof(f7,plain,(
% 1.30/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.30/0.99    inference(flattening,[],[f6])).
% 1.30/0.99  
% 1.30/0.99  fof(f26,plain,(
% 1.30/0.99    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.30/0.99    inference(cnf_transformation,[],[f7])).
% 1.30/0.99  
% 1.30/0.99  fof(f46,plain,(
% 1.30/0.99    v3_pre_topc(sK4,sK1)),
% 1.30/0.99    inference(cnf_transformation,[],[f25])).
% 1.30/0.99  
% 1.30/0.99  cnf(c_2,plain,
% 1.30/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.30/0.99      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.30/0.99      | v2_struct_0(X1)
% 1.30/0.99      | ~ v2_pre_topc(X1)
% 1.30/0.99      | ~ l1_pre_topc(X1) ),
% 1.30/0.99      inference(cnf_transformation,[],[f29]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_10,negated_conjecture,
% 1.30/0.99      ( r2_hidden(sK5,sK4) ),
% 1.30/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_351,plain,
% 1.30/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.30/0.99      | v2_struct_0(X1)
% 1.30/0.99      | ~ v2_pre_topc(X1)
% 1.30/0.99      | ~ l1_pre_topc(X1)
% 1.30/0.99      | k1_tops_1(X1,X0) != sK4
% 1.30/0.99      | sK5 != X2 ),
% 1.30/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_10]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_352,plain,
% 1.30/0.99      ( m1_connsp_2(X0,X1,sK5)
% 1.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/0.99      | ~ m1_subset_1(sK5,u1_struct_0(X1))
% 1.30/0.99      | v2_struct_0(X1)
% 1.30/0.99      | ~ v2_pre_topc(X1)
% 1.30/0.99      | ~ l1_pre_topc(X1)
% 1.30/0.99      | k1_tops_1(X1,X0) != sK4 ),
% 1.30/0.99      inference(unflattening,[status(thm)],[c_351]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_18,negated_conjecture,
% 1.30/0.99      ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 1.30/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_5,plain,
% 1.30/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.30/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.30/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.30/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 1.30/0.99      | ~ m1_pre_topc(X4,X0)
% 1.30/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.30/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.30/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.30/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.30/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.30/0.99      | ~ v1_funct_1(X2)
% 1.30/0.99      | v2_struct_0(X1)
% 1.30/0.99      | v2_struct_0(X0)
% 1.30/0.99      | v2_struct_0(X4)
% 1.30/0.99      | ~ v2_pre_topc(X1)
% 1.30/0.99      | ~ v2_pre_topc(X0)
% 1.30/0.99      | ~ l1_pre_topc(X0)
% 1.30/0.99      | ~ l1_pre_topc(X1) ),
% 1.30/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_9,negated_conjecture,
% 1.30/0.99      ( r1_tarski(sK4,u1_struct_0(sK3)) ),
% 1.30/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_386,plain,
% 1.30/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.30/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.30/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.30/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 1.30/0.99      | ~ m1_pre_topc(X4,X0)
% 1.30/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.30/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.30/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.30/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.30/0.99      | ~ v1_funct_1(X2)
% 1.30/0.99      | v2_struct_0(X1)
% 1.30/0.99      | v2_struct_0(X0)
% 1.30/0.99      | v2_struct_0(X4)
% 1.30/0.99      | ~ v2_pre_topc(X1)
% 1.30/0.99      | ~ v2_pre_topc(X0)
% 1.30/0.99      | ~ l1_pre_topc(X1)
% 1.30/0.99      | ~ l1_pre_topc(X0)
% 1.30/0.99      | u1_struct_0(X4) != u1_struct_0(sK3)
% 1.30/0.99      | sK4 != X5 ),
% 1.30/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_9]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_387,plain,
% 1.30/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.30/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.30/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.30/0.99      | ~ m1_connsp_2(sK4,X0,X3)
% 1.30/0.99      | ~ m1_pre_topc(X4,X0)
% 1.30/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.30/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.30/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.30/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 1.30/0.99      | ~ v1_funct_1(X2)
% 1.30/0.99      | v2_struct_0(X1)
% 1.30/0.99      | v2_struct_0(X0)
% 1.30/0.99      | v2_struct_0(X4)
% 1.30/0.99      | ~ v2_pre_topc(X1)
% 1.30/0.99      | ~ v2_pre_topc(X0)
% 1.30/0.99      | ~ l1_pre_topc(X1)
% 1.30/0.99      | ~ l1_pre_topc(X0)
% 1.30/0.99      | u1_struct_0(X4) != u1_struct_0(sK3) ),
% 1.30/0.99      inference(unflattening,[status(thm)],[c_386]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_15,negated_conjecture,
% 1.30/0.99      ( m1_pre_topc(sK3,sK1) ),
% 1.30/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_556,plain,
% 1.30/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.30/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.30/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.30/0.99      | ~ m1_connsp_2(sK4,X0,X3)
% 1.30/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.30/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.30/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.30/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 1.30/0.99      | ~ v1_funct_1(X2)
% 1.30/0.99      | v2_struct_0(X1)
% 1.30/0.99      | v2_struct_0(X0)
% 1.30/0.99      | v2_struct_0(X4)
% 1.30/0.99      | ~ v2_pre_topc(X1)
% 1.30/0.99      | ~ v2_pre_topc(X0)
% 1.30/0.99      | ~ l1_pre_topc(X1)
% 1.30/0.99      | ~ l1_pre_topc(X0)
% 1.30/0.99      | u1_struct_0(X4) != u1_struct_0(sK3)
% 1.30/0.99      | sK1 != X0
% 1.30/0.99      | sK3 != X4 ),
% 1.30/0.99      inference(resolution_lifted,[status(thm)],[c_387,c_15]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_557,plain,
% 1.30/0.99      ( ~ r1_tmap_1(sK1,X0,X1,X2)
% 1.30/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.30/0.99      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
% 1.30/0.99      | ~ m1_connsp_2(sK4,sK1,X2)
% 1.30/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.30/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.30/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.30/0.99      | ~ v1_funct_1(X1)
% 1.30/0.99      | v2_struct_0(X0)
% 1.30/0.99      | v2_struct_0(sK1)
% 1.30/0.99      | v2_struct_0(sK3)
% 1.30/0.99      | ~ v2_pre_topc(X0)
% 1.30/0.99      | ~ v2_pre_topc(sK1)
% 1.30/0.99      | ~ l1_pre_topc(X0)
% 1.30/0.99      | ~ l1_pre_topc(sK1)
% 1.30/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.30/0.99      inference(unflattening,[status(thm)],[c_556]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_22,negated_conjecture,
% 1.30/0.99      ( ~ v2_struct_0(sK1) ),
% 1.30/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_21,negated_conjecture,
% 1.30/0.99      ( v2_pre_topc(sK1) ),
% 1.30/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_20,negated_conjecture,
% 1.30/0.99      ( l1_pre_topc(sK1) ),
% 1.30/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_16,negated_conjecture,
% 1.30/0.99      ( ~ v2_struct_0(sK3) ),
% 1.30/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_14,negated_conjecture,
% 1.30/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.30/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_561,plain,
% 1.30/0.99      ( ~ l1_pre_topc(X0)
% 1.30/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.30/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.30/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/0.99      | ~ m1_connsp_2(sK4,sK1,X2)
% 1.30/0.99      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
% 1.30/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.30/0.99      | ~ r1_tmap_1(sK1,X0,X1,X2)
% 1.30/0.99      | ~ v1_funct_1(X1)
% 1.30/0.99      | v2_struct_0(X0)
% 1.30/0.99      | ~ v2_pre_topc(X0)
% 1.30/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.30/0.99      inference(global_propositional_subsumption,
% 1.30/0.99                [status(thm)],
% 1.30/0.99                [c_557,c_22,c_21,c_20,c_16,c_14]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_562,plain,
% 1.30/0.99      ( ~ r1_tmap_1(sK1,X0,X1,X2)
% 1.30/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.30/0.99      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
% 1.30/0.99      | ~ m1_connsp_2(sK4,sK1,X2)
% 1.30/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.30/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.30/0.99      | ~ v1_funct_1(X1)
% 1.30/0.99      | v2_struct_0(X0)
% 1.30/0.99      | ~ v2_pre_topc(X0)
% 1.30/0.99      | ~ l1_pre_topc(X0)
% 1.30/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.30/0.99      inference(renaming,[status(thm)],[c_561]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_606,plain,
% 1.30/0.99      ( ~ r1_tmap_1(sK1,X0,X1,X2)
% 1.30/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.30/0.99      | ~ m1_connsp_2(sK4,sK1,X2)
% 1.30/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.30/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.30/0.99      | ~ v1_funct_1(X1)
% 1.30/0.99      | v2_struct_0(X0)
% 1.30/0.99      | ~ v2_pre_topc(X0)
% 1.30/0.99      | ~ l1_pre_topc(X0)
% 1.30/0.99      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.30/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.30/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.30/0.99      | sK2 != X1 ),
% 1.30/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_562]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_607,plain,
% 1.30/0.99      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.30/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.30/0.99      | ~ m1_connsp_2(sK4,sK1,X1)
% 1.30/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.30/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.30/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/0.99      | ~ v1_funct_1(sK2)
% 1.30/0.99      | v2_struct_0(X0)
% 1.30/0.99      | ~ v2_pre_topc(X0)
% 1.30/0.99      | ~ l1_pre_topc(X0)
% 1.30/0.99      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.30/0.99      inference(unflattening,[status(thm)],[c_606]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_19,negated_conjecture,
% 1.30/0.99      ( v1_funct_1(sK2) ),
% 1.30/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_611,plain,
% 1.30/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.30/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.30/0.99      | ~ m1_connsp_2(sK4,sK1,X1)
% 1.30/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.30/0.99      | ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.30/0.99      | v2_struct_0(X0)
% 1.30/0.99      | ~ v2_pre_topc(X0)
% 1.30/0.99      | ~ l1_pre_topc(X0)
% 1.30/0.99      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.30/0.99      inference(global_propositional_subsumption,[status(thm)],[c_607,c_19]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_612,plain,
% 1.30/0.99      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.30/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.30/0.99      | ~ m1_connsp_2(sK4,sK1,X1)
% 1.30/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.30/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.30/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/0.99      | v2_struct_0(X0)
% 1.30/0.99      | ~ v2_pre_topc(X0)
% 1.30/0.99      | ~ l1_pre_topc(X0)
% 1.30/0.99      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.30/0.99      inference(renaming,[status(thm)],[c_611]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_751,plain,
% 1.30/0.99      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.30/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.30/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.30/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.30/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.30/0.99      | ~ m1_subset_1(sK5,u1_struct_0(X3))
% 1.30/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/0.99      | v2_struct_0(X3)
% 1.30/0.99      | v2_struct_0(X0)
% 1.30/0.99      | ~ v2_pre_topc(X3)
% 1.30/0.99      | ~ v2_pre_topc(X0)
% 1.30/0.99      | ~ l1_pre_topc(X0)
% 1.30/0.99      | ~ l1_pre_topc(X3)
% 1.30/0.99      | k1_tops_1(X3,X2) != sK4
% 1.30/0.99      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.30/0.99      | sK4 != X2
% 1.30/0.99      | sK5 != X1
% 1.30/0.99      | sK1 != X3 ),
% 1.30/0.99      inference(resolution_lifted,[status(thm)],[c_352,c_612]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_752,plain,
% 1.30/0.99      ( ~ r1_tmap_1(sK1,X0,sK2,sK5)
% 1.30/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
% 1.30/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.30/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
% 1.30/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/0.99      | v2_struct_0(X0)
% 1.30/0.99      | v2_struct_0(sK1)
% 1.30/0.99      | ~ v2_pre_topc(X0)
% 1.30/0.99      | ~ v2_pre_topc(sK1)
% 1.30/0.99      | ~ l1_pre_topc(X0)
% 1.30/0.99      | ~ l1_pre_topc(sK1)
% 1.30/0.99      | k1_tops_1(sK1,sK4) != sK4
% 1.30/0.99      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.30/0.99      inference(unflattening,[status(thm)],[c_751]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_13,negated_conjecture,
% 1.30/0.99      ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
% 1.30/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_756,plain,
% 1.30/0.99      ( ~ l1_pre_topc(X0)
% 1.30/0.99      | v2_struct_0(X0)
% 1.30/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
% 1.30/0.99      | ~ r1_tmap_1(sK1,X0,sK2,sK5)
% 1.30/0.99      | ~ v2_pre_topc(X0)
% 1.30/0.99      | k1_tops_1(sK1,sK4) != sK4
% 1.30/0.99      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.30/0.99      inference(global_propositional_subsumption,
% 1.30/0.99                [status(thm)],
% 1.30/0.99                [c_752,c_22,c_21,c_20,c_14,c_13]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_757,plain,
% 1.30/0.99      ( ~ r1_tmap_1(sK1,X0,sK2,sK5)
% 1.30/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
% 1.30/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/0.99      | v2_struct_0(X0)
% 1.30/0.99      | ~ v2_pre_topc(X0)
% 1.30/0.99      | ~ l1_pre_topc(X0)
% 1.30/0.99      | k1_tops_1(sK1,sK4) != sK4
% 1.30/0.99      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.30/0.99      inference(renaming,[status(thm)],[c_756]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_23,negated_conjecture,
% 1.30/0.99      ( l1_pre_topc(sK0) ),
% 1.30/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_898,plain,
% 1.30/0.99      ( ~ r1_tmap_1(sK1,X0,sK2,sK5)
% 1.30/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
% 1.30/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/0.99      | v2_struct_0(X0)
% 1.30/0.99      | ~ v2_pre_topc(X0)
% 1.30/0.99      | k1_tops_1(sK1,sK4) != sK4
% 1.30/0.99      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.30/0.99      | sK0 != X0 ),
% 1.30/0.99      inference(resolution_lifted,[status(thm)],[c_757,c_23]) ).
% 1.30/0.99  
% 1.30/0.99  cnf(c_899,plain,
% 1.30/0.99      ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.30/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.30/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.30/0.99      | v2_struct_0(sK0)
% 1.30/0.99      | ~ v2_pre_topc(sK0)
% 1.30/0.99      | k1_tops_1(sK1,sK4) != sK4
% 1.30/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.30/0.99      inference(unflattening,[status(thm)],[c_898]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_25,negated_conjecture,
% 1.30/1.00      ( ~ v2_struct_0(sK0) ),
% 1.30/1.00      inference(cnf_transformation,[],[f32]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_24,negated_conjecture,
% 1.30/1.00      ( v2_pre_topc(sK0) ),
% 1.30/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_17,negated_conjecture,
% 1.30/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 1.30/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_901,plain,
% 1.30/1.00      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.30/1.00      | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.30/1.00      | k1_tops_1(sK1,sK4) != sK4
% 1.30/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.30/1.00      inference(global_propositional_subsumption,
% 1.30/1.00                [status(thm)],
% 1.30/1.00                [c_899,c_25,c_24,c_17]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_902,plain,
% 1.30/1.00      ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.30/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.30/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/1.00      | k1_tops_1(sK1,sK4) != sK4
% 1.30/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.30/1.00      inference(renaming,[status(thm)],[c_901]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_990,plain,
% 1.30/1.00      ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.30/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.30/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/1.00      | k1_tops_1(sK1,sK4) != sK4 ),
% 1.30/1.00      inference(equality_resolution_simp,[status(thm)],[c_902]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1092,plain,
% 1.30/1.00      ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.30/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.30/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/1.00      | k1_tops_1(sK1,sK4) != sK4 ),
% 1.30/1.00      inference(subtyping,[status(esa)],[c_990]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1441,plain,
% 1.30/1.00      ( k1_tops_1(sK1,sK4) != sK4
% 1.30/1.00      | r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
% 1.30/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top
% 1.30/1.00      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 1.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1092]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_8,negated_conjecture,
% 1.30/1.00      ( sK5 = sK6 ),
% 1.30/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1102,negated_conjecture,
% 1.30/1.00      ( sK5 = sK6 ),
% 1.30/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1479,plain,
% 1.30/1.00      ( k1_tops_1(sK1,sK4) != sK4
% 1.30/1.00      | r1_tmap_1(sK1,sK0,sK2,sK6) != iProver_top
% 1.30/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) = iProver_top
% 1.30/1.00      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
% 1.30/1.00      inference(light_normalisation,[status(thm)],[c_1441,c_1102]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_12,negated_conjecture,
% 1.30/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.30/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1101,negated_conjecture,
% 1.30/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.30/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1432,plain,
% 1.30/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1101]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_4,plain,
% 1.30/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 1.30/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.30/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.30/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 1.30/1.00      | ~ m1_pre_topc(X4,X0)
% 1.30/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.30/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.30/1.00      | ~ v1_funct_1(X2)
% 1.30/1.00      | v2_struct_0(X1)
% 1.30/1.00      | v2_struct_0(X0)
% 1.30/1.00      | v2_struct_0(X4)
% 1.30/1.00      | ~ v2_pre_topc(X1)
% 1.30/1.00      | ~ v2_pre_topc(X0)
% 1.30/1.00      | ~ l1_pre_topc(X0)
% 1.30/1.00      | ~ l1_pre_topc(X1) ),
% 1.30/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_446,plain,
% 1.30/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 1.30/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.30/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.30/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 1.30/1.00      | ~ m1_pre_topc(X4,X0)
% 1.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.30/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.30/1.00      | ~ v1_funct_1(X2)
% 1.30/1.00      | v2_struct_0(X1)
% 1.30/1.00      | v2_struct_0(X0)
% 1.30/1.00      | v2_struct_0(X4)
% 1.30/1.00      | ~ v2_pre_topc(X1)
% 1.30/1.00      | ~ v2_pre_topc(X0)
% 1.30/1.00      | ~ l1_pre_topc(X1)
% 1.30/1.00      | ~ l1_pre_topc(X0)
% 1.30/1.00      | u1_struct_0(X4) != u1_struct_0(sK3)
% 1.30/1.00      | sK4 != X5 ),
% 1.30/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_9]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_447,plain,
% 1.30/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 1.30/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.30/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.30/1.00      | ~ m1_connsp_2(sK4,X0,X3)
% 1.30/1.00      | ~ m1_pre_topc(X4,X0)
% 1.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 1.30/1.00      | ~ v1_funct_1(X2)
% 1.30/1.00      | v2_struct_0(X1)
% 1.30/1.00      | v2_struct_0(X0)
% 1.30/1.00      | v2_struct_0(X4)
% 1.30/1.00      | ~ v2_pre_topc(X1)
% 1.30/1.00      | ~ v2_pre_topc(X0)
% 1.30/1.00      | ~ l1_pre_topc(X1)
% 1.30/1.00      | ~ l1_pre_topc(X0)
% 1.30/1.00      | u1_struct_0(X4) != u1_struct_0(sK3) ),
% 1.30/1.00      inference(unflattening,[status(thm)],[c_446]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_508,plain,
% 1.30/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 1.30/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.30/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.30/1.00      | ~ m1_connsp_2(sK4,X0,X3)
% 1.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 1.30/1.00      | ~ v1_funct_1(X2)
% 1.30/1.00      | v2_struct_0(X1)
% 1.30/1.00      | v2_struct_0(X0)
% 1.30/1.00      | v2_struct_0(X4)
% 1.30/1.00      | ~ v2_pre_topc(X1)
% 1.30/1.00      | ~ v2_pre_topc(X0)
% 1.30/1.00      | ~ l1_pre_topc(X1)
% 1.30/1.00      | ~ l1_pre_topc(X0)
% 1.30/1.00      | u1_struct_0(X4) != u1_struct_0(sK3)
% 1.30/1.00      | sK1 != X0
% 1.30/1.00      | sK3 != X4 ),
% 1.30/1.00      inference(resolution_lifted,[status(thm)],[c_447,c_15]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_509,plain,
% 1.30/1.00      ( r1_tmap_1(sK1,X0,X1,X2)
% 1.30/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.30/1.00      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
% 1.30/1.00      | ~ m1_connsp_2(sK4,sK1,X2)
% 1.30/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.30/1.00      | ~ v1_funct_1(X1)
% 1.30/1.00      | v2_struct_0(X0)
% 1.30/1.00      | v2_struct_0(sK1)
% 1.30/1.00      | v2_struct_0(sK3)
% 1.30/1.00      | ~ v2_pre_topc(X0)
% 1.30/1.00      | ~ v2_pre_topc(sK1)
% 1.30/1.00      | ~ l1_pre_topc(X0)
% 1.30/1.00      | ~ l1_pre_topc(sK1)
% 1.30/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.30/1.00      inference(unflattening,[status(thm)],[c_508]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_513,plain,
% 1.30/1.00      ( ~ l1_pre_topc(X0)
% 1.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.30/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/1.00      | ~ m1_connsp_2(sK4,sK1,X2)
% 1.30/1.00      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
% 1.30/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.30/1.00      | r1_tmap_1(sK1,X0,X1,X2)
% 1.30/1.00      | ~ v1_funct_1(X1)
% 1.30/1.00      | v2_struct_0(X0)
% 1.30/1.00      | ~ v2_pre_topc(X0)
% 1.30/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.30/1.00      inference(global_propositional_subsumption,
% 1.30/1.00                [status(thm)],
% 1.30/1.00                [c_509,c_22,c_21,c_20,c_16,c_14]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_514,plain,
% 1.30/1.00      ( r1_tmap_1(sK1,X0,X1,X2)
% 1.30/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.30/1.00      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
% 1.30/1.00      | ~ m1_connsp_2(sK4,sK1,X2)
% 1.30/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.30/1.00      | ~ v1_funct_1(X1)
% 1.30/1.00      | v2_struct_0(X0)
% 1.30/1.00      | ~ v2_pre_topc(X0)
% 1.30/1.00      | ~ l1_pre_topc(X0)
% 1.30/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.30/1.00      inference(renaming,[status(thm)],[c_513]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_648,plain,
% 1.30/1.00      ( r1_tmap_1(sK1,X0,X1,X2)
% 1.30/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.30/1.00      | ~ m1_connsp_2(sK4,sK1,X2)
% 1.30/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.30/1.00      | ~ v1_funct_1(X1)
% 1.30/1.00      | v2_struct_0(X0)
% 1.30/1.00      | ~ v2_pre_topc(X0)
% 1.30/1.00      | ~ l1_pre_topc(X0)
% 1.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.30/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.30/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.30/1.00      | sK2 != X1 ),
% 1.30/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_514]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_649,plain,
% 1.30/1.00      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.30/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.30/1.00      | ~ m1_connsp_2(sK4,sK1,X1)
% 1.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.30/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/1.00      | ~ v1_funct_1(sK2)
% 1.30/1.00      | v2_struct_0(X0)
% 1.30/1.00      | ~ v2_pre_topc(X0)
% 1.30/1.00      | ~ l1_pre_topc(X0)
% 1.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.30/1.00      inference(unflattening,[status(thm)],[c_648]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_653,plain,
% 1.30/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.30/1.00      | ~ m1_connsp_2(sK4,sK1,X1)
% 1.30/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.30/1.00      | r1_tmap_1(sK1,X0,sK2,X1)
% 1.30/1.00      | v2_struct_0(X0)
% 1.30/1.00      | ~ v2_pre_topc(X0)
% 1.30/1.00      | ~ l1_pre_topc(X0)
% 1.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.30/1.00      inference(global_propositional_subsumption,[status(thm)],[c_649,c_19]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_654,plain,
% 1.30/1.00      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.30/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.30/1.00      | ~ m1_connsp_2(sK4,sK1,X1)
% 1.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.30/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/1.00      | v2_struct_0(X0)
% 1.30/1.00      | ~ v2_pre_topc(X0)
% 1.30/1.00      | ~ l1_pre_topc(X0)
% 1.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.30/1.00      inference(renaming,[status(thm)],[c_653]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_712,plain,
% 1.30/1.00      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.30/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.30/1.00      | ~ m1_subset_1(sK5,u1_struct_0(X3))
% 1.30/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/1.00      | v2_struct_0(X3)
% 1.30/1.00      | v2_struct_0(X0)
% 1.30/1.00      | ~ v2_pre_topc(X3)
% 1.30/1.00      | ~ v2_pre_topc(X0)
% 1.30/1.00      | ~ l1_pre_topc(X0)
% 1.30/1.00      | ~ l1_pre_topc(X3)
% 1.30/1.00      | k1_tops_1(X3,X2) != sK4
% 1.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.30/1.00      | sK4 != X2
% 1.30/1.00      | sK5 != X1
% 1.30/1.00      | sK1 != X3 ),
% 1.30/1.00      inference(resolution_lifted,[status(thm)],[c_352,c_654]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_713,plain,
% 1.30/1.00      ( r1_tmap_1(sK1,X0,sK2,sK5)
% 1.30/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
% 1.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.30/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
% 1.30/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/1.00      | v2_struct_0(X0)
% 1.30/1.00      | v2_struct_0(sK1)
% 1.30/1.00      | ~ v2_pre_topc(X0)
% 1.30/1.00      | ~ v2_pre_topc(sK1)
% 1.30/1.00      | ~ l1_pre_topc(X0)
% 1.30/1.00      | ~ l1_pre_topc(sK1)
% 1.30/1.00      | k1_tops_1(sK1,sK4) != sK4
% 1.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.30/1.00      inference(unflattening,[status(thm)],[c_712]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_717,plain,
% 1.30/1.00      ( ~ l1_pre_topc(X0)
% 1.30/1.00      | v2_struct_0(X0)
% 1.30/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
% 1.30/1.00      | r1_tmap_1(sK1,X0,sK2,sK5)
% 1.30/1.00      | ~ v2_pre_topc(X0)
% 1.30/1.00      | k1_tops_1(sK1,sK4) != sK4
% 1.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.30/1.00      inference(global_propositional_subsumption,
% 1.30/1.00                [status(thm)],
% 1.30/1.00                [c_713,c_22,c_21,c_20,c_14,c_13]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_718,plain,
% 1.30/1.00      ( r1_tmap_1(sK1,X0,sK2,sK5)
% 1.30/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
% 1.30/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/1.00      | v2_struct_0(X0)
% 1.30/1.00      | ~ v2_pre_topc(X0)
% 1.30/1.00      | ~ l1_pre_topc(X0)
% 1.30/1.00      | k1_tops_1(sK1,sK4) != sK4
% 1.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.30/1.00      inference(renaming,[status(thm)],[c_717]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_921,plain,
% 1.30/1.00      ( r1_tmap_1(sK1,X0,sK2,sK5)
% 1.30/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),sK5)
% 1.30/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.30/1.00      | v2_struct_0(X0)
% 1.30/1.00      | ~ v2_pre_topc(X0)
% 1.30/1.00      | k1_tops_1(sK1,sK4) != sK4
% 1.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.30/1.00      | sK0 != X0 ),
% 1.30/1.00      inference(resolution_lifted,[status(thm)],[c_718,c_23]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_922,plain,
% 1.30/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.30/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.30/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.30/1.00      | v2_struct_0(sK0)
% 1.30/1.00      | ~ v2_pre_topc(sK0)
% 1.30/1.00      | k1_tops_1(sK1,sK4) != sK4
% 1.30/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.30/1.00      inference(unflattening,[status(thm)],[c_921]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_924,plain,
% 1.30/1.00      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.30/1.00      | r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.30/1.00      | k1_tops_1(sK1,sK4) != sK4
% 1.30/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.30/1.00      inference(global_propositional_subsumption,
% 1.30/1.00                [status(thm)],
% 1.30/1.00                [c_922,c_25,c_24,c_17]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_925,plain,
% 1.30/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.30/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.30/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/1.00      | k1_tops_1(sK1,sK4) != sK4
% 1.30/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.30/1.00      inference(renaming,[status(thm)],[c_924]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_988,plain,
% 1.30/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.30/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.30/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/1.00      | k1_tops_1(sK1,sK4) != sK4 ),
% 1.30/1.00      inference(equality_resolution_simp,[status(thm)],[c_925]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1093,plain,
% 1.30/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.30/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.30/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.30/1.00      | k1_tops_1(sK1,sK4) != sK4 ),
% 1.30/1.00      inference(subtyping,[status(esa)],[c_988]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1440,plain,
% 1.30/1.00      ( k1_tops_1(sK1,sK4) != sK4
% 1.30/1.00      | r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
% 1.30/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top
% 1.30/1.00      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 1.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1093]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1471,plain,
% 1.30/1.00      ( k1_tops_1(sK1,sK4) != sK4
% 1.30/1.00      | r1_tmap_1(sK1,sK0,sK2,sK6) = iProver_top
% 1.30/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) != iProver_top
% 1.30/1.00      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
% 1.30/1.00      inference(light_normalisation,[status(thm)],[c_1440,c_1102]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_6,negated_conjecture,
% 1.30/1.00      ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.30/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) ),
% 1.30/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1104,negated_conjecture,
% 1.30/1.00      ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.30/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) ),
% 1.30/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1430,plain,
% 1.30/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
% 1.30/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) != iProver_top ),
% 1.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1104]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1466,plain,
% 1.30/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK6) != iProver_top
% 1.30/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) != iProver_top ),
% 1.30/1.00      inference(light_normalisation,[status(thm)],[c_1430,c_1102]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1476,plain,
% 1.30/1.00      ( k1_tops_1(sK1,sK4) != sK4
% 1.30/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) != iProver_top ),
% 1.30/1.00      inference(forward_subsumption_resolution,
% 1.30/1.00                [status(thm)],
% 1.30/1.00                [c_1471,c_1432,c_1466]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_7,negated_conjecture,
% 1.30/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.30/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) ),
% 1.30/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1103,negated_conjecture,
% 1.30/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.30/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) ),
% 1.30/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1431,plain,
% 1.30/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
% 1.30/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) = iProver_top ),
% 1.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1103]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1461,plain,
% 1.30/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK6) = iProver_top
% 1.30/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) = iProver_top ),
% 1.30/1.00      inference(light_normalisation,[status(thm)],[c_1431,c_1102]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1484,plain,
% 1.30/1.00      ( k1_tops_1(sK1,sK4) != sK4 ),
% 1.30/1.00      inference(forward_subsumption_resolution,
% 1.30/1.00                [status(thm)],
% 1.30/1.00                [c_1479,c_1432,c_1476,c_1461]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1,plain,
% 1.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.30/1.00      | ~ v3_pre_topc(X0,X1)
% 1.30/1.00      | ~ v2_pre_topc(X3)
% 1.30/1.00      | ~ l1_pre_topc(X1)
% 1.30/1.00      | ~ l1_pre_topc(X3)
% 1.30/1.00      | k1_tops_1(X1,X0) = X0 ),
% 1.30/1.00      inference(cnf_transformation,[],[f26]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_11,negated_conjecture,
% 1.30/1.00      ( v3_pre_topc(sK4,sK1) ),
% 1.30/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_321,plain,
% 1.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.30/1.00      | ~ v2_pre_topc(X1)
% 1.30/1.00      | ~ l1_pre_topc(X1)
% 1.30/1.00      | ~ l1_pre_topc(X3)
% 1.30/1.00      | k1_tops_1(X3,X2) = X2
% 1.30/1.00      | sK4 != X2
% 1.30/1.00      | sK1 != X3 ),
% 1.30/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_11]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_322,plain,
% 1.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.30/1.00      | ~ v2_pre_topc(X1)
% 1.30/1.00      | ~ l1_pre_topc(X1)
% 1.30/1.00      | ~ l1_pre_topc(sK1)
% 1.30/1.00      | k1_tops_1(sK1,sK4) = sK4 ),
% 1.30/1.00      inference(unflattening,[status(thm)],[c_321]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_326,plain,
% 1.30/1.00      ( ~ l1_pre_topc(X1)
% 1.30/1.00      | ~ v2_pre_topc(X1)
% 1.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.00      | k1_tops_1(sK1,sK4) = sK4 ),
% 1.30/1.00      inference(global_propositional_subsumption,
% 1.30/1.00                [status(thm)],
% 1.30/1.00                [c_322,c_20,c_14]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_327,plain,
% 1.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.00      | ~ v2_pre_topc(X1)
% 1.30/1.00      | ~ l1_pre_topc(X1)
% 1.30/1.00      | k1_tops_1(sK1,sK4) = sK4 ),
% 1.30/1.00      inference(renaming,[status(thm)],[c_326]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_810,plain,
% 1.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.00      | ~ v2_pre_topc(X1)
% 1.30/1.00      | k1_tops_1(sK1,sK4) = sK4
% 1.30/1.00      | sK1 != X1 ),
% 1.30/1.00      inference(resolution_lifted,[status(thm)],[c_327,c_20]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_811,plain,
% 1.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.30/1.00      | ~ v2_pre_topc(sK1)
% 1.30/1.00      | k1_tops_1(sK1,sK4) = sK4 ),
% 1.30/1.00      inference(unflattening,[status(thm)],[c_810]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_815,plain,
% 1.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.30/1.00      | k1_tops_1(sK1,sK4) = sK4 ),
% 1.30/1.00      inference(global_propositional_subsumption,[status(thm)],[c_811,c_21]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1097,plain,
% 1.30/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.30/1.00      | k1_tops_1(sK1,sK4) = sK4 ),
% 1.30/1.00      inference(subtyping,[status(esa)],[c_815]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1436,plain,
% 1.30/1.00      ( k1_tops_1(sK1,sK4) = sK4
% 1.30/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1097]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1486,plain,
% 1.30/1.00      ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.30/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_1484,c_1436]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1099,negated_conjecture,
% 1.30/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.30/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1434,plain,
% 1.30/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1099]) ).
% 1.30/1.00  
% 1.30/1.00  cnf(c_1492,plain,
% 1.30/1.00      ( $false ),
% 1.30/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_1486,c_1434]) ).
% 1.30/1.00  
% 1.30/1.00  
% 1.30/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.30/1.00  
% 1.30/1.00  ------                               Statistics
% 1.30/1.00  
% 1.30/1.00  ------ General
% 1.30/1.00  
% 1.30/1.00  abstr_ref_over_cycles:                  0
% 1.30/1.00  abstr_ref_under_cycles:                 0
% 1.30/1.00  gc_basic_clause_elim:                   0
% 1.30/1.00  forced_gc_time:                         0
% 1.30/1.00  parsing_time:                           0.009
% 1.30/1.00  unif_index_cands_time:                  0.
% 1.30/1.00  unif_index_add_time:                    0.
% 1.30/1.00  orderings_time:                         0.
% 1.30/1.00  out_proof_time:                         0.012
% 1.30/1.00  total_time:                             0.079
% 1.30/1.00  num_of_symbols:                         58
% 1.30/1.00  num_of_terms:                           1083
% 1.30/1.00  
% 1.30/1.00  ------ Preprocessing
% 1.30/1.00  
% 1.30/1.00  num_of_splits:                          0
% 1.30/1.00  num_of_split_atoms:                     0
% 1.30/1.00  num_of_reused_defs:                     0
% 1.30/1.00  num_eq_ax_congr_red:                    12
% 1.30/1.00  num_of_sem_filtered_clauses:            1
% 1.30/1.00  num_of_subtypes:                        3
% 1.30/1.00  monotx_restored_types:                  0
% 1.30/1.00  sat_num_of_epr_types:                   0
% 1.30/1.00  sat_num_of_non_cyclic_types:            0
% 1.30/1.00  sat_guarded_non_collapsed_types:        0
% 1.30/1.00  num_pure_diseq_elim:                    0
% 1.30/1.00  simp_replaced_by:                       0
% 1.30/1.00  res_preprocessed:                       86
% 1.30/1.00  prep_upred:                             0
% 1.30/1.00  prep_unflattend:                        25
% 1.30/1.00  smt_new_axioms:                         0
% 1.30/1.00  pred_elim_cands:                        2
% 1.30/1.00  pred_elim:                              10
% 1.30/1.00  pred_elim_cl:                           13
% 1.30/1.00  pred_elim_cycles:                       12
% 1.30/1.00  merged_defs:                            8
% 1.30/1.00  merged_defs_ncl:                        0
% 1.30/1.00  bin_hyper_res:                          8
% 1.30/1.00  prep_cycles:                            4
% 1.30/1.00  pred_elim_time:                         0.02
% 1.30/1.00  splitting_time:                         0.
% 1.30/1.00  sem_filter_time:                        0.
% 1.30/1.00  monotx_time:                            0.
% 1.30/1.00  subtype_inf_time:                       0.
% 1.30/1.00  
% 1.30/1.00  ------ Problem properties
% 1.30/1.00  
% 1.30/1.00  clauses:                                13
% 1.30/1.00  conjectures:                            7
% 1.30/1.00  epr:                                    1
% 1.30/1.00  horn:                                   12
% 1.30/1.00  ground:                                 11
% 1.30/1.00  unary:                                  5
% 1.30/1.00  binary:                                 4
% 1.30/1.00  lits:                                   33
% 1.30/1.00  lits_eq:                                9
% 1.30/1.00  fd_pure:                                0
% 1.30/1.00  fd_pseudo:                              0
% 1.30/1.00  fd_cond:                                0
% 1.30/1.00  fd_pseudo_cond:                         0
% 1.30/1.00  ac_symbols:                             0
% 1.30/1.00  
% 1.30/1.00  ------ Propositional Solver
% 1.30/1.00  
% 1.30/1.00  prop_solver_calls:                      21
% 1.30/1.00  prop_fast_solver_calls:                 735
% 1.30/1.00  smt_solver_calls:                       0
% 1.30/1.00  smt_fast_solver_calls:                  0
% 1.30/1.00  prop_num_of_clauses:                    204
% 1.30/1.00  prop_preprocess_simplified:             1536
% 1.30/1.00  prop_fo_subsumed:                       36
% 1.30/1.00  prop_solver_time:                       0.
% 1.30/1.00  smt_solver_time:                        0.
% 1.30/1.00  smt_fast_solver_time:                   0.
% 1.30/1.00  prop_fast_solver_time:                  0.
% 1.30/1.00  prop_unsat_core_time:                   0.
% 1.30/1.00  
% 1.30/1.00  ------ QBF
% 1.30/1.00  
% 1.30/1.00  qbf_q_res:                              0
% 1.30/1.00  qbf_num_tautologies:                    0
% 1.30/1.00  qbf_prep_cycles:                        0
% 1.30/1.00  
% 1.30/1.00  ------ BMC1
% 1.30/1.00  
% 1.30/1.00  bmc1_current_bound:                     -1
% 1.30/1.00  bmc1_last_solved_bound:                 -1
% 1.30/1.00  bmc1_unsat_core_size:                   -1
% 1.30/1.00  bmc1_unsat_core_parents_size:           -1
% 1.30/1.00  bmc1_merge_next_fun:                    0
% 1.30/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.30/1.00  
% 1.30/1.00  ------ Instantiation
% 1.30/1.00  
% 1.30/1.00  inst_num_of_clauses:                    23
% 1.30/1.00  inst_num_in_passive:                    0
% 1.30/1.00  inst_num_in_active:                     0
% 1.30/1.00  inst_num_in_unprocessed:                23
% 1.30/1.00  inst_num_of_loops:                      0
% 1.30/1.00  inst_num_of_learning_restarts:          0
% 1.30/1.00  inst_num_moves_active_passive:          0
% 1.30/1.00  inst_lit_activity:                      0
% 1.30/1.00  inst_lit_activity_moves:                0
% 1.30/1.00  inst_num_tautologies:                   0
% 1.30/1.00  inst_num_prop_implied:                  0
% 1.30/1.00  inst_num_existing_simplified:           0
% 1.30/1.00  inst_num_eq_res_simplified:             0
% 1.30/1.00  inst_num_child_elim:                    0
% 1.30/1.00  inst_num_of_dismatching_blockings:      0
% 1.30/1.00  inst_num_of_non_proper_insts:           0
% 1.30/1.00  inst_num_of_duplicates:                 0
% 1.30/1.00  inst_inst_num_from_inst_to_res:         0
% 1.30/1.00  inst_dismatching_checking_time:         0.
% 1.30/1.00  
% 1.30/1.00  ------ Resolution
% 1.30/1.00  
% 1.30/1.00  res_num_of_clauses:                     0
% 1.30/1.00  res_num_in_passive:                     0
% 1.30/1.00  res_num_in_active:                      0
% 1.30/1.00  res_num_of_loops:                       90
% 1.30/1.00  res_forward_subset_subsumed:            0
% 1.30/1.00  res_backward_subset_subsumed:           0
% 1.30/1.00  res_forward_subsumed:                   0
% 1.30/1.00  res_backward_subsumed:                  0
% 1.30/1.00  res_forward_subsumption_resolution:     0
% 1.30/1.00  res_backward_subsumption_resolution:    0
% 1.30/1.00  res_clause_to_clause_subsumption:       40
% 1.30/1.00  res_orphan_elimination:                 0
% 1.30/1.00  res_tautology_del:                      18
% 1.30/1.00  res_num_eq_res_simplified:              2
% 1.30/1.00  res_num_sel_changes:                    0
% 1.30/1.00  res_moves_from_active_to_pass:          0
% 1.30/1.00  
% 1.30/1.00  ------ Superposition
% 1.30/1.00  
% 1.30/1.00  sup_time_total:                         0.
% 1.30/1.00  sup_time_generating:                    0.
% 1.30/1.00  sup_time_sim_full:                      0.
% 1.30/1.00  sup_time_sim_immed:                     0.
% 1.30/1.00  
% 1.30/1.00  sup_num_of_clauses:                     0
% 1.30/1.00  sup_num_in_active:                      0
% 1.30/1.00  sup_num_in_passive:                     0
% 1.30/1.00  sup_num_of_loops:                       0
% 1.30/1.00  sup_fw_superposition:                   0
% 1.30/1.00  sup_bw_superposition:                   0
% 1.30/1.00  sup_immediate_simplified:               0
% 1.30/1.00  sup_given_eliminated:                   0
% 1.30/1.00  comparisons_done:                       0
% 1.30/1.00  comparisons_avoided:                    0
% 1.30/1.00  
% 1.30/1.00  ------ Simplifications
% 1.30/1.00  
% 1.30/1.00  
% 1.30/1.00  sim_fw_subset_subsumed:                 0
% 1.30/1.00  sim_bw_subset_subsumed:                 1
% 1.30/1.00  sim_fw_subsumed:                        0
% 1.30/1.00  sim_bw_subsumed:                        0
% 1.30/1.00  sim_fw_subsumption_res:                 5
% 1.30/1.00  sim_bw_subsumption_res:                 3
% 1.30/1.00  sim_tautology_del:                      0
% 1.30/1.00  sim_eq_tautology_del:                   0
% 1.30/1.00  sim_eq_res_simp:                        0
% 1.30/1.00  sim_fw_demodulated:                     0
% 1.30/1.00  sim_bw_demodulated:                     0
% 1.30/1.00  sim_light_normalised:                   5
% 1.30/1.00  sim_joinable_taut:                      0
% 1.30/1.00  sim_joinable_simp:                      0
% 1.30/1.00  sim_ac_normalised:                      0
% 1.30/1.00  sim_smt_subsumption:                    0
% 1.30/1.00  
%------------------------------------------------------------------------------
