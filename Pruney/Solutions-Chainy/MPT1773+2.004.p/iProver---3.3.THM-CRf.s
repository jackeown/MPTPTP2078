%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:08 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  217 (1681 expanded)
%              Number of clauses        :  128 ( 277 expanded)
%              Number of leaves         :   22 ( 759 expanded)
%              Depth                    :   26
%              Number of atoms          : 1737 (36423 expanded)
%              Number of equality atoms :  289 (2373 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   50 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
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

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK0(X0,X1,X2))
                    & r1_tarski(sK0(X0,X1,X2),X2)
                    & v3_pre_topc(sK0(X0,X1,X2),X0)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f54,plain,(
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
     => ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8)
          | ~ r1_tmap_1(X3,X1,X4,X6) )
        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8)
          | r1_tmap_1(X3,X1,X4,X6) )
        & sK8 = X6
        & r1_tarski(X5,u1_struct_0(X2))
        & r2_hidden(X6,X5)
        & v3_pre_topc(X5,X3)
        & m1_subset_1(sK8,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
              | ~ r1_tmap_1(X3,X1,X4,sK7) )
            & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
              | r1_tmap_1(X3,X1,X4,sK7) )
            & sK7 = X7
            & r1_tarski(X5,u1_struct_0(X2))
            & r2_hidden(sK7,X5)
            & v3_pre_topc(X5,X3)
            & m1_subset_1(X7,u1_struct_0(X2)) )
        & m1_subset_1(sK7,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
                & r1_tarski(sK6,u1_struct_0(X2))
                & r2_hidden(X6,sK6)
                & v3_pre_topc(sK6,X3)
                & m1_subset_1(X7,u1_struct_0(X2)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
                    ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X7)
                      | ~ r1_tmap_1(X3,X1,sK5,X6) )
                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X7)
                      | r1_tmap_1(X3,X1,sK5,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(X2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,X3)
                    & m1_subset_1(X7,u1_struct_0(X2)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
                        ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X7)
                          | ~ r1_tmap_1(sK4,X1,X4,X6) )
                        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X7)
                          | r1_tmap_1(sK4,X1,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(X2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,sK4)
                        & m1_subset_1(X7,u1_struct_0(X2)) )
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK4))) )
            & m1_pre_topc(X2,sK4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
                            ( ( ~ r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X7)
                              | ~ r1_tmap_1(X3,X1,X4,X6) )
                            & ( r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X7)
                              | r1_tmap_1(X3,X1,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(sK3))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,X3)
                            & m1_subset_1(X7,u1_struct_0(sK3)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                & m1_pre_topc(sK3,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
                                ( ( ~ r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,sK2,X4,X6) )
                                & ( r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,sK2,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,X3)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
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
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X7)
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
                  & m1_pre_topc(X3,sK1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ( ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
      | ~ r1_tmap_1(sK4,sK2,sK5,sK7) )
    & ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
      | r1_tmap_1(sK4,sK2,sK5,sK7) )
    & sK7 = sK8
    & r1_tarski(sK6,u1_struct_0(sK3))
    & r2_hidden(sK7,sK6)
    & v3_pre_topc(sK6,sK4)
    & m1_subset_1(sK8,u1_struct_0(sK3))
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    & m1_pre_topc(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK1)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f46,f54,f53,f52,f51,f50,f49,f48,f47])).

fof(f84,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f55])).

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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f79,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f55])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f77,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f83,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f97,plain,
    ( ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
    | ~ r1_tmap_1(sK4,sK2,sK5,sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f95,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f102,plain,(
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
    inference(equality_resolution,[],[f72])).

fof(f10,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f100,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f96,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
    | r1_tmap_1(sK4,sK2,sK5,sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,(
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
    inference(equality_resolution,[],[f73])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f93,plain,(
    r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f55])).

fof(f94,plain,(
    r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    v3_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_8,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4055,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(sK6,sK4)
    | ~ r2_hidden(X1,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(sK6,X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5824,plain,
    ( m1_connsp_2(X0,sK4,sK8)
    | ~ v3_pre_topc(sK6,sK4)
    | ~ r2_hidden(sK8,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK4))
    | ~ r1_tarski(sK6,X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_4055])).

cnf(c_6854,plain,
    ( m1_connsp_2(sK6,sK4,sK8)
    | ~ v3_pre_topc(sK6,sK4)
    | ~ r2_hidden(sK8,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK4))
    | ~ r1_tarski(sK6,sK6)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_5824])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3001,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3003,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_929,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X4) != u1_struct_0(sK2)
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_30])).

cnf(c_930,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_929])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_934,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_930,c_31])).

cnf(c_935,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_934])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_966,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_935,c_18])).

cnf(c_2985,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_966])).

cnf(c_3885,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k3_tmap_1(X2,X0,sK4,X1,sK5)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2985])).

cnf(c_6041,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK4,X0,sK5)
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3885])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_45,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_46,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_47,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_54,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6681,plain,
    ( v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK4,X0,sK5)
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6041,c_45,c_46,c_47,c_54])).

cnf(c_6682,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK4,X0,sK5)
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6681])).

cnf(c_6693,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k3_tmap_1(X0,sK2,sK4,sK3,sK5)
    | m1_pre_topc(sK4,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3003,c_6682])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_980,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK2)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_30])).

cnf(c_981,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_980])).

cnf(c_985,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_981,c_31])).

cnf(c_986,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_985])).

cnf(c_2984,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK5,X2)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_986])).

cnf(c_3605,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2984])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_43,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_44,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_50,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_51,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3446,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3447,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3446])).

cnf(c_3449,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3447])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3480,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3481,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3480])).

cnf(c_3483,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3481])).

cnf(c_5398,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3605,c_43,c_44,c_50,c_51,c_3449,c_3483])).

cnf(c_5399,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5398])).

cnf(c_5409,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK2,sK5,X0)
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5399])).

cnf(c_5950,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK2,sK5,X0)
    | m1_pre_topc(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5409,c_45,c_46,c_47,c_54])).

cnf(c_5958,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK2,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_3003,c_5950])).

cnf(c_6694,plain,
    ( k3_tmap_1(X0,sK2,sK4,sK3,sK5) = k2_tmap_1(sK4,sK2,sK5,sK3)
    | m1_pre_topc(sK4,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6693,c_5958])).

cnf(c_6758,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_tmap_1(sK4,sK2,sK5,sK3)
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3001,c_6694])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_42,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_6761,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_tmap_1(sK4,sK2,sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6758,c_42,c_43,c_44])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK7)
    | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3011,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3086,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3011,c_21])).

cnf(c_6765,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6761,c_3086])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_48,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_55,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_58,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_105,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_109,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2077,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_2092,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2077])).

cnf(c_2068,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3804,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2068])).

cnf(c_17,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_15,plain,
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
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_217,plain,
    ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_15])).

cnf(c_218,plain,
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
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_217])).

cnf(c_757,plain,
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
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_218,c_30])).

cnf(c_758,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_757])).

cnf(c_762,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_758,c_31])).

cnf(c_763,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_762])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_798,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_763,c_6])).

cnf(c_3421,plain,
    ( r1_tmap_1(X0,sK2,k2_tmap_1(X1,sK2,sK5,X0),X2)
    | ~ r1_tmap_1(X1,sK2,sK5,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_4334,plain,
    ( ~ r1_tmap_1(sK4,sK2,sK5,X0)
    | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),X0)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3421])).

cnf(c_4468,plain,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK8)
    | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4334])).

cnf(c_4469,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8) = iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4468])).

cnf(c_6831,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6765,c_43,c_44,c_45,c_46,c_47,c_48,c_50,c_51,c_54,c_55,c_58,c_105,c_109,c_2092,c_3449,c_3483,c_3804,c_4469])).

cnf(c_6833,plain,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6831])).

cnf(c_20,negated_conjecture,
    ( r1_tmap_1(sK4,sK2,sK5,sK7)
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3010,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3075,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8) = iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3010,c_21])).

cnf(c_6764,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8) = iProver_top
    | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6761,c_3075])).

cnf(c_6774,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8)
    | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6764])).

cnf(c_16,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_814,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_30])).

cnf(c_815,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_814])).

cnf(c_819,plain,
    ( ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_connsp_2(X4,X2,X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_815,c_31])).

cnf(c_820,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_819])).

cnf(c_861,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_820,c_6])).

cnf(c_3431,plain,
    ( ~ r1_tmap_1(X0,sK2,k2_tmap_1(X1,sK2,sK5,X0),X2)
    | r1_tmap_1(X1,sK2,sK5,X2)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | ~ r1_tarski(X3,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_4352,plain,
    ( r1_tmap_1(sK4,sK2,sK5,X0)
    | ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),X0)
    | ~ m1_connsp_2(X1,sK4,X0)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ r1_tarski(X1,u1_struct_0(sK3))
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3431])).

cnf(c_4531,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8)
    | ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8)
    | ~ m1_connsp_2(X0,sK4,sK8)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ r1_tarski(X0,u1_struct_0(sK3))
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4352])).

cnf(c_5454,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8)
    | ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8)
    | ~ m1_connsp_2(sK6,sK4,sK8)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ r1_tarski(sK6,u1_struct_0(sK3))
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4531])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_4455,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3482,plain,
    ( ~ m1_pre_topc(sK4,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3480])).

cnf(c_3448,plain,
    ( ~ m1_pre_topc(sK4,sK1)
    | l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3446])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3008,plain,
    ( r2_hidden(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3047,plain,
    ( r2_hidden(sK8,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3008,c_21])).

cnf(c_3315,plain,
    ( r2_hidden(sK8,sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3047])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3005,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3052,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3005,c_21])).

cnf(c_3313,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3052])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_24,negated_conjecture,
    ( v3_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f89])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6854,c_6833,c_6774,c_5454,c_4455,c_3804,c_3482,c_3448,c_3315,c_3313,c_2092,c_109,c_105,c_22,c_24,c_25,c_27,c_28,c_29,c_32,c_33,c_35,c_36,c_37,c_38,c_39,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:41:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.61/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.00  
% 2.61/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.61/1.00  
% 2.61/1.00  ------  iProver source info
% 2.61/1.00  
% 2.61/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.61/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.61/1.00  git: non_committed_changes: false
% 2.61/1.00  git: last_make_outside_of_git: false
% 2.61/1.00  
% 2.61/1.00  ------ 
% 2.61/1.00  
% 2.61/1.00  ------ Input Options
% 2.61/1.00  
% 2.61/1.00  --out_options                           all
% 2.61/1.00  --tptp_safe_out                         true
% 2.61/1.00  --problem_path                          ""
% 2.61/1.00  --include_path                          ""
% 2.61/1.00  --clausifier                            res/vclausify_rel
% 2.61/1.00  --clausifier_options                    --mode clausify
% 2.61/1.00  --stdin                                 false
% 2.61/1.00  --stats_out                             all
% 2.61/1.00  
% 2.61/1.00  ------ General Options
% 2.61/1.00  
% 2.61/1.00  --fof                                   false
% 2.61/1.00  --time_out_real                         305.
% 2.61/1.00  --time_out_virtual                      -1.
% 2.61/1.00  --symbol_type_check                     false
% 2.61/1.00  --clausify_out                          false
% 2.61/1.00  --sig_cnt_out                           false
% 2.61/1.00  --trig_cnt_out                          false
% 2.61/1.00  --trig_cnt_out_tolerance                1.
% 2.61/1.00  --trig_cnt_out_sk_spl                   false
% 2.61/1.00  --abstr_cl_out                          false
% 2.61/1.00  
% 2.61/1.00  ------ Global Options
% 2.61/1.00  
% 2.61/1.00  --schedule                              default
% 2.61/1.00  --add_important_lit                     false
% 2.61/1.00  --prop_solver_per_cl                    1000
% 2.61/1.00  --min_unsat_core                        false
% 2.61/1.00  --soft_assumptions                      false
% 2.61/1.00  --soft_lemma_size                       3
% 2.61/1.00  --prop_impl_unit_size                   0
% 2.61/1.00  --prop_impl_unit                        []
% 2.61/1.00  --share_sel_clauses                     true
% 2.61/1.00  --reset_solvers                         false
% 2.61/1.00  --bc_imp_inh                            [conj_cone]
% 2.61/1.00  --conj_cone_tolerance                   3.
% 2.61/1.00  --extra_neg_conj                        none
% 2.61/1.00  --large_theory_mode                     true
% 2.61/1.00  --prolific_symb_bound                   200
% 2.61/1.00  --lt_threshold                          2000
% 2.61/1.00  --clause_weak_htbl                      true
% 2.61/1.00  --gc_record_bc_elim                     false
% 2.61/1.00  
% 2.61/1.00  ------ Preprocessing Options
% 2.61/1.00  
% 2.61/1.00  --preprocessing_flag                    true
% 2.61/1.00  --time_out_prep_mult                    0.1
% 2.61/1.00  --splitting_mode                        input
% 2.61/1.00  --splitting_grd                         true
% 2.61/1.00  --splitting_cvd                         false
% 2.61/1.00  --splitting_cvd_svl                     false
% 2.61/1.00  --splitting_nvd                         32
% 2.61/1.00  --sub_typing                            true
% 2.61/1.00  --prep_gs_sim                           true
% 2.61/1.00  --prep_unflatten                        true
% 2.61/1.00  --prep_res_sim                          true
% 2.61/1.00  --prep_upred                            true
% 2.61/1.00  --prep_sem_filter                       exhaustive
% 2.61/1.00  --prep_sem_filter_out                   false
% 2.61/1.00  --pred_elim                             true
% 2.61/1.00  --res_sim_input                         true
% 2.61/1.00  --eq_ax_congr_red                       true
% 2.61/1.00  --pure_diseq_elim                       true
% 2.61/1.00  --brand_transform                       false
% 2.61/1.00  --non_eq_to_eq                          false
% 2.61/1.00  --prep_def_merge                        true
% 2.61/1.00  --prep_def_merge_prop_impl              false
% 2.61/1.00  --prep_def_merge_mbd                    true
% 2.61/1.00  --prep_def_merge_tr_red                 false
% 2.61/1.00  --prep_def_merge_tr_cl                  false
% 2.61/1.00  --smt_preprocessing                     true
% 2.61/1.00  --smt_ac_axioms                         fast
% 2.61/1.00  --preprocessed_out                      false
% 2.61/1.00  --preprocessed_stats                    false
% 2.61/1.00  
% 2.61/1.00  ------ Abstraction refinement Options
% 2.61/1.00  
% 2.61/1.00  --abstr_ref                             []
% 2.61/1.00  --abstr_ref_prep                        false
% 2.61/1.00  --abstr_ref_until_sat                   false
% 2.61/1.00  --abstr_ref_sig_restrict                funpre
% 2.61/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.61/1.00  --abstr_ref_under                       []
% 2.61/1.00  
% 2.61/1.00  ------ SAT Options
% 2.61/1.00  
% 2.61/1.00  --sat_mode                              false
% 2.61/1.00  --sat_fm_restart_options                ""
% 2.61/1.00  --sat_gr_def                            false
% 2.61/1.00  --sat_epr_types                         true
% 2.61/1.00  --sat_non_cyclic_types                  false
% 2.61/1.00  --sat_finite_models                     false
% 2.61/1.00  --sat_fm_lemmas                         false
% 2.61/1.00  --sat_fm_prep                           false
% 2.61/1.00  --sat_fm_uc_incr                        true
% 2.61/1.00  --sat_out_model                         small
% 2.61/1.00  --sat_out_clauses                       false
% 2.61/1.00  
% 2.61/1.00  ------ QBF Options
% 2.61/1.00  
% 2.61/1.00  --qbf_mode                              false
% 2.61/1.00  --qbf_elim_univ                         false
% 2.61/1.00  --qbf_dom_inst                          none
% 2.61/1.00  --qbf_dom_pre_inst                      false
% 2.61/1.00  --qbf_sk_in                             false
% 2.61/1.00  --qbf_pred_elim                         true
% 2.61/1.00  --qbf_split                             512
% 2.61/1.00  
% 2.61/1.00  ------ BMC1 Options
% 2.61/1.00  
% 2.61/1.00  --bmc1_incremental                      false
% 2.61/1.00  --bmc1_axioms                           reachable_all
% 2.61/1.00  --bmc1_min_bound                        0
% 2.61/1.00  --bmc1_max_bound                        -1
% 2.61/1.00  --bmc1_max_bound_default                -1
% 2.61/1.00  --bmc1_symbol_reachability              true
% 2.61/1.00  --bmc1_property_lemmas                  false
% 2.61/1.00  --bmc1_k_induction                      false
% 2.61/1.00  --bmc1_non_equiv_states                 false
% 2.61/1.00  --bmc1_deadlock                         false
% 2.61/1.00  --bmc1_ucm                              false
% 2.61/1.00  --bmc1_add_unsat_core                   none
% 2.61/1.00  --bmc1_unsat_core_children              false
% 2.61/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.61/1.00  --bmc1_out_stat                         full
% 2.61/1.00  --bmc1_ground_init                      false
% 2.61/1.00  --bmc1_pre_inst_next_state              false
% 2.61/1.00  --bmc1_pre_inst_state                   false
% 2.61/1.00  --bmc1_pre_inst_reach_state             false
% 2.61/1.00  --bmc1_out_unsat_core                   false
% 2.61/1.00  --bmc1_aig_witness_out                  false
% 2.61/1.00  --bmc1_verbose                          false
% 2.61/1.00  --bmc1_dump_clauses_tptp                false
% 2.61/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.61/1.00  --bmc1_dump_file                        -
% 2.61/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.61/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.61/1.00  --bmc1_ucm_extend_mode                  1
% 2.61/1.00  --bmc1_ucm_init_mode                    2
% 2.61/1.00  --bmc1_ucm_cone_mode                    none
% 2.61/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.61/1.00  --bmc1_ucm_relax_model                  4
% 2.61/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.61/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.61/1.00  --bmc1_ucm_layered_model                none
% 2.61/1.00  --bmc1_ucm_max_lemma_size               10
% 2.61/1.00  
% 2.61/1.00  ------ AIG Options
% 2.61/1.00  
% 2.61/1.00  --aig_mode                              false
% 2.61/1.00  
% 2.61/1.00  ------ Instantiation Options
% 2.61/1.00  
% 2.61/1.00  --instantiation_flag                    true
% 2.61/1.00  --inst_sos_flag                         false
% 2.61/1.00  --inst_sos_phase                        true
% 2.61/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.61/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.61/1.00  --inst_lit_sel_side                     num_symb
% 2.61/1.00  --inst_solver_per_active                1400
% 2.61/1.00  --inst_solver_calls_frac                1.
% 2.61/1.00  --inst_passive_queue_type               priority_queues
% 2.61/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.61/1.00  --inst_passive_queues_freq              [25;2]
% 2.61/1.00  --inst_dismatching                      true
% 2.61/1.00  --inst_eager_unprocessed_to_passive     true
% 2.61/1.00  --inst_prop_sim_given                   true
% 2.61/1.00  --inst_prop_sim_new                     false
% 2.61/1.00  --inst_subs_new                         false
% 2.61/1.00  --inst_eq_res_simp                      false
% 2.61/1.00  --inst_subs_given                       false
% 2.61/1.00  --inst_orphan_elimination               true
% 2.61/1.00  --inst_learning_loop_flag               true
% 2.61/1.00  --inst_learning_start                   3000
% 2.61/1.00  --inst_learning_factor                  2
% 2.61/1.00  --inst_start_prop_sim_after_learn       3
% 2.61/1.00  --inst_sel_renew                        solver
% 2.61/1.00  --inst_lit_activity_flag                true
% 2.61/1.00  --inst_restr_to_given                   false
% 2.61/1.00  --inst_activity_threshold               500
% 2.61/1.00  --inst_out_proof                        true
% 2.61/1.00  
% 2.61/1.00  ------ Resolution Options
% 2.61/1.00  
% 2.61/1.00  --resolution_flag                       true
% 2.61/1.00  --res_lit_sel                           adaptive
% 2.61/1.00  --res_lit_sel_side                      none
% 2.61/1.00  --res_ordering                          kbo
% 2.61/1.00  --res_to_prop_solver                    active
% 2.61/1.00  --res_prop_simpl_new                    false
% 2.61/1.00  --res_prop_simpl_given                  true
% 2.61/1.00  --res_passive_queue_type                priority_queues
% 2.61/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.61/1.00  --res_passive_queues_freq               [15;5]
% 2.61/1.00  --res_forward_subs                      full
% 2.61/1.00  --res_backward_subs                     full
% 2.61/1.00  --res_forward_subs_resolution           true
% 2.61/1.00  --res_backward_subs_resolution          true
% 2.61/1.00  --res_orphan_elimination                true
% 2.61/1.00  --res_time_limit                        2.
% 2.61/1.00  --res_out_proof                         true
% 2.61/1.00  
% 2.61/1.00  ------ Superposition Options
% 2.61/1.00  
% 2.61/1.00  --superposition_flag                    true
% 2.61/1.00  --sup_passive_queue_type                priority_queues
% 2.61/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.61/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.61/1.00  --demod_completeness_check              fast
% 2.61/1.00  --demod_use_ground                      true
% 2.61/1.00  --sup_to_prop_solver                    passive
% 2.61/1.00  --sup_prop_simpl_new                    true
% 2.61/1.00  --sup_prop_simpl_given                  true
% 2.61/1.00  --sup_fun_splitting                     false
% 2.61/1.00  --sup_smt_interval                      50000
% 2.61/1.00  
% 2.61/1.00  ------ Superposition Simplification Setup
% 2.61/1.00  
% 2.61/1.00  --sup_indices_passive                   []
% 2.61/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.61/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.00  --sup_full_bw                           [BwDemod]
% 2.61/1.00  --sup_immed_triv                        [TrivRules]
% 2.61/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.61/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.00  --sup_immed_bw_main                     []
% 2.61/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.61/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/1.00  
% 2.61/1.00  ------ Combination Options
% 2.61/1.00  
% 2.61/1.00  --comb_res_mult                         3
% 2.61/1.00  --comb_sup_mult                         2
% 2.61/1.00  --comb_inst_mult                        10
% 2.61/1.00  
% 2.61/1.00  ------ Debug Options
% 2.61/1.00  
% 2.61/1.00  --dbg_backtrace                         false
% 2.61/1.00  --dbg_dump_prop_clauses                 false
% 2.61/1.00  --dbg_dump_prop_clauses_file            -
% 2.61/1.00  --dbg_out_stat                          false
% 2.61/1.00  ------ Parsing...
% 2.61/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.61/1.00  
% 2.61/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.61/1.00  
% 2.61/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.61/1.00  
% 2.61/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.61/1.00  ------ Proving...
% 2.61/1.00  ------ Problem Properties 
% 2.61/1.00  
% 2.61/1.00  
% 2.61/1.00  clauses                                 38
% 2.61/1.00  conjectures                             21
% 2.61/1.00  EPR                                     19
% 2.61/1.00  Horn                                    26
% 2.61/1.00  unary                                   20
% 2.61/1.00  binary                                  2
% 2.61/1.00  lits                                    142
% 2.61/1.00  lits eq                                 12
% 2.61/1.00  fd_pure                                 0
% 2.61/1.00  fd_pseudo                               0
% 2.61/1.00  fd_cond                                 0
% 2.61/1.00  fd_pseudo_cond                          1
% 2.61/1.00  AC symbols                              0
% 2.61/1.00  
% 2.61/1.00  ------ Schedule dynamic 5 is on 
% 2.61/1.00  
% 2.61/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.61/1.00  
% 2.61/1.00  
% 2.61/1.00  ------ 
% 2.61/1.00  Current options:
% 2.61/1.00  ------ 
% 2.61/1.00  
% 2.61/1.00  ------ Input Options
% 2.61/1.00  
% 2.61/1.00  --out_options                           all
% 2.61/1.00  --tptp_safe_out                         true
% 2.61/1.00  --problem_path                          ""
% 2.61/1.00  --include_path                          ""
% 2.61/1.00  --clausifier                            res/vclausify_rel
% 2.61/1.00  --clausifier_options                    --mode clausify
% 2.61/1.00  --stdin                                 false
% 2.61/1.00  --stats_out                             all
% 2.61/1.00  
% 2.61/1.00  ------ General Options
% 2.61/1.00  
% 2.61/1.00  --fof                                   false
% 2.61/1.00  --time_out_real                         305.
% 2.61/1.00  --time_out_virtual                      -1.
% 2.61/1.00  --symbol_type_check                     false
% 2.61/1.00  --clausify_out                          false
% 2.61/1.00  --sig_cnt_out                           false
% 2.61/1.00  --trig_cnt_out                          false
% 2.61/1.00  --trig_cnt_out_tolerance                1.
% 2.61/1.00  --trig_cnt_out_sk_spl                   false
% 2.61/1.00  --abstr_cl_out                          false
% 2.61/1.00  
% 2.61/1.00  ------ Global Options
% 2.61/1.00  
% 2.61/1.00  --schedule                              default
% 2.61/1.00  --add_important_lit                     false
% 2.61/1.00  --prop_solver_per_cl                    1000
% 2.61/1.00  --min_unsat_core                        false
% 2.61/1.00  --soft_assumptions                      false
% 2.61/1.00  --soft_lemma_size                       3
% 2.61/1.00  --prop_impl_unit_size                   0
% 2.61/1.00  --prop_impl_unit                        []
% 2.61/1.00  --share_sel_clauses                     true
% 2.61/1.00  --reset_solvers                         false
% 2.61/1.00  --bc_imp_inh                            [conj_cone]
% 2.61/1.00  --conj_cone_tolerance                   3.
% 2.61/1.00  --extra_neg_conj                        none
% 2.61/1.00  --large_theory_mode                     true
% 2.61/1.00  --prolific_symb_bound                   200
% 2.61/1.00  --lt_threshold                          2000
% 2.61/1.00  --clause_weak_htbl                      true
% 2.61/1.00  --gc_record_bc_elim                     false
% 2.61/1.00  
% 2.61/1.00  ------ Preprocessing Options
% 2.61/1.00  
% 2.61/1.00  --preprocessing_flag                    true
% 2.61/1.00  --time_out_prep_mult                    0.1
% 2.61/1.00  --splitting_mode                        input
% 2.61/1.00  --splitting_grd                         true
% 2.61/1.00  --splitting_cvd                         false
% 2.61/1.00  --splitting_cvd_svl                     false
% 2.61/1.00  --splitting_nvd                         32
% 2.61/1.00  --sub_typing                            true
% 2.61/1.00  --prep_gs_sim                           true
% 2.61/1.00  --prep_unflatten                        true
% 2.61/1.00  --prep_res_sim                          true
% 2.61/1.00  --prep_upred                            true
% 2.61/1.00  --prep_sem_filter                       exhaustive
% 2.61/1.00  --prep_sem_filter_out                   false
% 2.61/1.00  --pred_elim                             true
% 2.61/1.00  --res_sim_input                         true
% 2.61/1.00  --eq_ax_congr_red                       true
% 2.61/1.00  --pure_diseq_elim                       true
% 2.61/1.00  --brand_transform                       false
% 2.61/1.00  --non_eq_to_eq                          false
% 2.61/1.00  --prep_def_merge                        true
% 2.61/1.00  --prep_def_merge_prop_impl              false
% 2.61/1.00  --prep_def_merge_mbd                    true
% 2.61/1.00  --prep_def_merge_tr_red                 false
% 2.61/1.00  --prep_def_merge_tr_cl                  false
% 2.61/1.00  --smt_preprocessing                     true
% 2.61/1.00  --smt_ac_axioms                         fast
% 2.61/1.00  --preprocessed_out                      false
% 2.61/1.00  --preprocessed_stats                    false
% 2.61/1.00  
% 2.61/1.00  ------ Abstraction refinement Options
% 2.61/1.00  
% 2.61/1.00  --abstr_ref                             []
% 2.61/1.00  --abstr_ref_prep                        false
% 2.61/1.00  --abstr_ref_until_sat                   false
% 2.61/1.00  --abstr_ref_sig_restrict                funpre
% 2.61/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.61/1.00  --abstr_ref_under                       []
% 2.61/1.00  
% 2.61/1.00  ------ SAT Options
% 2.61/1.00  
% 2.61/1.00  --sat_mode                              false
% 2.61/1.00  --sat_fm_restart_options                ""
% 2.61/1.00  --sat_gr_def                            false
% 2.61/1.00  --sat_epr_types                         true
% 2.61/1.00  --sat_non_cyclic_types                  false
% 2.61/1.00  --sat_finite_models                     false
% 2.61/1.00  --sat_fm_lemmas                         false
% 2.61/1.00  --sat_fm_prep                           false
% 2.61/1.00  --sat_fm_uc_incr                        true
% 2.61/1.00  --sat_out_model                         small
% 2.61/1.00  --sat_out_clauses                       false
% 2.61/1.00  
% 2.61/1.00  ------ QBF Options
% 2.61/1.00  
% 2.61/1.00  --qbf_mode                              false
% 2.61/1.00  --qbf_elim_univ                         false
% 2.61/1.00  --qbf_dom_inst                          none
% 2.61/1.00  --qbf_dom_pre_inst                      false
% 2.61/1.00  --qbf_sk_in                             false
% 2.61/1.00  --qbf_pred_elim                         true
% 2.61/1.00  --qbf_split                             512
% 2.61/1.00  
% 2.61/1.00  ------ BMC1 Options
% 2.61/1.00  
% 2.61/1.00  --bmc1_incremental                      false
% 2.61/1.00  --bmc1_axioms                           reachable_all
% 2.61/1.00  --bmc1_min_bound                        0
% 2.61/1.00  --bmc1_max_bound                        -1
% 2.61/1.00  --bmc1_max_bound_default                -1
% 2.61/1.00  --bmc1_symbol_reachability              true
% 2.61/1.00  --bmc1_property_lemmas                  false
% 2.61/1.00  --bmc1_k_induction                      false
% 2.61/1.00  --bmc1_non_equiv_states                 false
% 2.61/1.00  --bmc1_deadlock                         false
% 2.61/1.00  --bmc1_ucm                              false
% 2.61/1.00  --bmc1_add_unsat_core                   none
% 2.61/1.00  --bmc1_unsat_core_children              false
% 2.61/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.61/1.00  --bmc1_out_stat                         full
% 2.61/1.00  --bmc1_ground_init                      false
% 2.61/1.00  --bmc1_pre_inst_next_state              false
% 2.61/1.00  --bmc1_pre_inst_state                   false
% 2.61/1.00  --bmc1_pre_inst_reach_state             false
% 2.61/1.00  --bmc1_out_unsat_core                   false
% 2.61/1.00  --bmc1_aig_witness_out                  false
% 2.61/1.00  --bmc1_verbose                          false
% 2.61/1.00  --bmc1_dump_clauses_tptp                false
% 2.61/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.61/1.00  --bmc1_dump_file                        -
% 2.61/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.61/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.61/1.00  --bmc1_ucm_extend_mode                  1
% 2.61/1.00  --bmc1_ucm_init_mode                    2
% 2.61/1.00  --bmc1_ucm_cone_mode                    none
% 2.61/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.61/1.00  --bmc1_ucm_relax_model                  4
% 2.61/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.61/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.61/1.00  --bmc1_ucm_layered_model                none
% 2.61/1.00  --bmc1_ucm_max_lemma_size               10
% 2.61/1.00  
% 2.61/1.00  ------ AIG Options
% 2.61/1.00  
% 2.61/1.00  --aig_mode                              false
% 2.61/1.00  
% 2.61/1.00  ------ Instantiation Options
% 2.61/1.00  
% 2.61/1.00  --instantiation_flag                    true
% 2.61/1.00  --inst_sos_flag                         false
% 2.61/1.00  --inst_sos_phase                        true
% 2.61/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.61/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.61/1.00  --inst_lit_sel_side                     none
% 2.61/1.00  --inst_solver_per_active                1400
% 2.61/1.00  --inst_solver_calls_frac                1.
% 2.61/1.00  --inst_passive_queue_type               priority_queues
% 2.61/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.61/1.00  --inst_passive_queues_freq              [25;2]
% 2.61/1.00  --inst_dismatching                      true
% 2.61/1.00  --inst_eager_unprocessed_to_passive     true
% 2.61/1.00  --inst_prop_sim_given                   true
% 2.61/1.00  --inst_prop_sim_new                     false
% 2.61/1.00  --inst_subs_new                         false
% 2.61/1.00  --inst_eq_res_simp                      false
% 2.61/1.00  --inst_subs_given                       false
% 2.61/1.00  --inst_orphan_elimination               true
% 2.61/1.00  --inst_learning_loop_flag               true
% 2.61/1.00  --inst_learning_start                   3000
% 2.61/1.00  --inst_learning_factor                  2
% 2.61/1.00  --inst_start_prop_sim_after_learn       3
% 2.61/1.00  --inst_sel_renew                        solver
% 2.61/1.00  --inst_lit_activity_flag                true
% 2.61/1.00  --inst_restr_to_given                   false
% 2.61/1.00  --inst_activity_threshold               500
% 2.61/1.00  --inst_out_proof                        true
% 2.61/1.00  
% 2.61/1.00  ------ Resolution Options
% 2.61/1.00  
% 2.61/1.00  --resolution_flag                       false
% 2.61/1.00  --res_lit_sel                           adaptive
% 2.61/1.00  --res_lit_sel_side                      none
% 2.61/1.00  --res_ordering                          kbo
% 2.61/1.00  --res_to_prop_solver                    active
% 2.61/1.00  --res_prop_simpl_new                    false
% 2.61/1.00  --res_prop_simpl_given                  true
% 2.61/1.00  --res_passive_queue_type                priority_queues
% 2.61/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.61/1.00  --res_passive_queues_freq               [15;5]
% 2.61/1.00  --res_forward_subs                      full
% 2.61/1.00  --res_backward_subs                     full
% 2.61/1.00  --res_forward_subs_resolution           true
% 2.61/1.00  --res_backward_subs_resolution          true
% 2.61/1.00  --res_orphan_elimination                true
% 2.61/1.00  --res_time_limit                        2.
% 2.61/1.00  --res_out_proof                         true
% 2.61/1.00  
% 2.61/1.00  ------ Superposition Options
% 2.61/1.00  
% 2.61/1.00  --superposition_flag                    true
% 2.61/1.00  --sup_passive_queue_type                priority_queues
% 2.61/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.61/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.61/1.00  --demod_completeness_check              fast
% 2.61/1.00  --demod_use_ground                      true
% 2.61/1.00  --sup_to_prop_solver                    passive
% 2.61/1.00  --sup_prop_simpl_new                    true
% 2.61/1.00  --sup_prop_simpl_given                  true
% 2.61/1.00  --sup_fun_splitting                     false
% 2.61/1.00  --sup_smt_interval                      50000
% 2.61/1.00  
% 2.61/1.00  ------ Superposition Simplification Setup
% 2.61/1.00  
% 2.61/1.00  --sup_indices_passive                   []
% 2.61/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.61/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.00  --sup_full_bw                           [BwDemod]
% 2.61/1.00  --sup_immed_triv                        [TrivRules]
% 2.61/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.61/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.00  --sup_immed_bw_main                     []
% 2.61/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.61/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/1.00  
% 2.61/1.00  ------ Combination Options
% 2.61/1.00  
% 2.61/1.00  --comb_res_mult                         3
% 2.61/1.00  --comb_sup_mult                         2
% 2.61/1.00  --comb_inst_mult                        10
% 2.61/1.00  
% 2.61/1.00  ------ Debug Options
% 2.61/1.00  
% 2.61/1.00  --dbg_backtrace                         false
% 2.61/1.00  --dbg_dump_prop_clauses                 false
% 2.61/1.00  --dbg_dump_prop_clauses_file            -
% 2.61/1.00  --dbg_out_stat                          false
% 2.61/1.00  
% 2.61/1.00  
% 2.61/1.00  
% 2.61/1.00  
% 2.61/1.00  ------ Proving...
% 2.61/1.00  
% 2.61/1.00  
% 2.61/1.00  % SZS status Theorem for theBenchmark.p
% 2.61/1.00  
% 2.61/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.61/1.00  
% 2.61/1.00  fof(f7,axiom,(
% 2.61/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 2.61/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f24,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.61/1.00    inference(ennf_transformation,[],[f7])).
% 2.61/1.00  
% 2.61/1.00  fof(f25,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.61/1.00    inference(flattening,[],[f24])).
% 2.61/1.00  
% 2.61/1.00  fof(f40,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.61/1.00    inference(nnf_transformation,[],[f25])).
% 2.61/1.00  
% 2.61/1.00  fof(f41,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.61/1.00    inference(rectify,[],[f40])).
% 2.61/1.00  
% 2.61/1.00  fof(f42,plain,(
% 2.61/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK0(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.61/1.00    introduced(choice_axiom,[])).
% 2.61/1.00  
% 2.61/1.00  fof(f43,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK0(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.61/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 2.61/1.00  
% 2.61/1.00  fof(f68,plain,(
% 2.61/1.00    ( ! [X2,X0,X3,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f43])).
% 2.61/1.00  
% 2.61/1.00  fof(f13,conjecture,(
% 2.61/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.61/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f14,negated_conjecture,(
% 2.61/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.61/1.00    inference(negated_conjecture,[],[f13])).
% 2.61/1.00  
% 2.61/1.00  fof(f36,plain,(
% 2.61/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.61/1.00    inference(ennf_transformation,[],[f14])).
% 2.61/1.00  
% 2.61/1.00  fof(f37,plain,(
% 2.61/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.61/1.00    inference(flattening,[],[f36])).
% 2.61/1.00  
% 2.61/1.00  fof(f45,plain,(
% 2.61/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.61/1.00    inference(nnf_transformation,[],[f37])).
% 2.61/1.00  
% 2.61/1.00  fof(f46,plain,(
% 2.61/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.61/1.00    inference(flattening,[],[f45])).
% 2.61/1.00  
% 2.61/1.00  fof(f54,plain,(
% 2.61/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8) | r1_tmap_1(X3,X1,X4,X6)) & sK8 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(sK8,u1_struct_0(X2)))) )),
% 2.61/1.00    introduced(choice_axiom,[])).
% 2.61/1.00  
% 2.61/1.00  fof(f53,plain,(
% 2.61/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,sK7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,sK7)) & sK7 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK7,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 2.61/1.00    introduced(choice_axiom,[])).
% 2.61/1.00  
% 2.61/1.00  fof(f52,plain,(
% 2.61/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(sK6,u1_struct_0(X2)) & r2_hidden(X6,sK6) & v3_pre_topc(sK6,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X3))))) )),
% 2.61/1.00    introduced(choice_axiom,[])).
% 2.61/1.00  
% 2.61/1.00  fof(f51,plain,(
% 2.61/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X7) | ~r1_tmap_1(X3,X1,sK5,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X7) | r1_tmap_1(X3,X1,sK5,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 2.61/1.00    introduced(choice_axiom,[])).
% 2.61/1.00  
% 2.61/1.00  fof(f50,plain,(
% 2.61/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X7) | ~r1_tmap_1(sK4,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X7) | r1_tmap_1(sK4,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK4) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_pre_topc(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.61/1.00    introduced(choice_axiom,[])).
% 2.61/1.00  
% 2.61/1.00  fof(f49,plain,(
% 2.61/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK3)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(sK3))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.61/1.00    introduced(choice_axiom,[])).
% 2.61/1.00  
% 2.61/1.00  fof(f48,plain,(
% 2.61/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK2,X4,X6)) & (r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X7) | r1_tmap_1(X3,sK2,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.61/1.00    introduced(choice_axiom,[])).
% 2.61/1.00  
% 2.61/1.00  fof(f47,plain,(
% 2.61/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.61/1.00    introduced(choice_axiom,[])).
% 2.61/1.00  
% 2.61/1.00  fof(f55,plain,(
% 2.61/1.00    ((((((((~r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK2,sK5,sK7)) & (r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK2,sK5,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK3)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK4) & m1_subset_1(sK8,u1_struct_0(sK3))) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_pre_topc(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.61/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f46,f54,f53,f52,f51,f50,f49,f48,f47])).
% 2.61/1.00  
% 2.61/1.00  fof(f84,plain,(
% 2.61/1.00    m1_pre_topc(sK4,sK1)),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f88,plain,(
% 2.61/1.00    m1_pre_topc(sK3,sK4)),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f9,axiom,(
% 2.61/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.61/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f28,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.61/1.00    inference(ennf_transformation,[],[f9])).
% 2.61/1.00  
% 2.61/1.00  fof(f29,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.61/1.00    inference(flattening,[],[f28])).
% 2.61/1.00  
% 2.61/1.00  fof(f70,plain,(
% 2.61/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f29])).
% 2.61/1.00  
% 2.61/1.00  fof(f86,plain,(
% 2.61/1.00    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f85,plain,(
% 2.61/1.00    v1_funct_1(sK5)),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f12,axiom,(
% 2.61/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.61/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f34,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.61/1.00    inference(ennf_transformation,[],[f12])).
% 2.61/1.00  
% 2.61/1.00  fof(f35,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.61/1.00    inference(flattening,[],[f34])).
% 2.61/1.00  
% 2.61/1.00  fof(f74,plain,(
% 2.61/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f35])).
% 2.61/1.00  
% 2.61/1.00  fof(f78,plain,(
% 2.61/1.00    ~v2_struct_0(sK2)),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f79,plain,(
% 2.61/1.00    v2_pre_topc(sK2)),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f80,plain,(
% 2.61/1.00    l1_pre_topc(sK2)),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f87,plain,(
% 2.61/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f8,axiom,(
% 2.61/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.61/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f26,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.61/1.00    inference(ennf_transformation,[],[f8])).
% 2.61/1.00  
% 2.61/1.00  fof(f27,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.61/1.00    inference(flattening,[],[f26])).
% 2.61/1.00  
% 2.61/1.00  fof(f69,plain,(
% 2.61/1.00    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f27])).
% 2.61/1.00  
% 2.61/1.00  fof(f76,plain,(
% 2.61/1.00    v2_pre_topc(sK1)),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f77,plain,(
% 2.61/1.00    l1_pre_topc(sK1)),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f83,plain,(
% 2.61/1.00    ~v2_struct_0(sK4)),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f4,axiom,(
% 2.61/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.61/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f19,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.61/1.00    inference(ennf_transformation,[],[f4])).
% 2.61/1.00  
% 2.61/1.00  fof(f61,plain,(
% 2.61/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f19])).
% 2.61/1.00  
% 2.61/1.00  fof(f3,axiom,(
% 2.61/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.61/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f17,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.61/1.00    inference(ennf_transformation,[],[f3])).
% 2.61/1.00  
% 2.61/1.00  fof(f18,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.61/1.00    inference(flattening,[],[f17])).
% 2.61/1.00  
% 2.61/1.00  fof(f60,plain,(
% 2.61/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f18])).
% 2.61/1.00  
% 2.61/1.00  fof(f75,plain,(
% 2.61/1.00    ~v2_struct_0(sK1)),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f97,plain,(
% 2.61/1.00    ~r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK2,sK5,sK7)),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f95,plain,(
% 2.61/1.00    sK7 = sK8),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f81,plain,(
% 2.61/1.00    ~v2_struct_0(sK3)),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f91,plain,(
% 2.61/1.00    m1_subset_1(sK8,u1_struct_0(sK3))),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f1,axiom,(
% 2.61/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.61/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f38,plain,(
% 2.61/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.61/1.00    inference(nnf_transformation,[],[f1])).
% 2.61/1.00  
% 2.61/1.00  fof(f39,plain,(
% 2.61/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.61/1.00    inference(flattening,[],[f38])).
% 2.61/1.00  
% 2.61/1.00  fof(f56,plain,(
% 2.61/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.61/1.00    inference(cnf_transformation,[],[f39])).
% 2.61/1.00  
% 2.61/1.00  fof(f99,plain,(
% 2.61/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.61/1.00    inference(equality_resolution,[],[f56])).
% 2.61/1.00  
% 2.61/1.00  fof(f58,plain,(
% 2.61/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f39])).
% 2.61/1.00  
% 2.61/1.00  fof(f11,axiom,(
% 2.61/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.61/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f32,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.61/1.00    inference(ennf_transformation,[],[f11])).
% 2.61/1.00  
% 2.61/1.00  fof(f33,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.61/1.00    inference(flattening,[],[f32])).
% 2.61/1.00  
% 2.61/1.00  fof(f44,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.61/1.00    inference(nnf_transformation,[],[f33])).
% 2.61/1.00  
% 2.61/1.00  fof(f72,plain,(
% 2.61/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f44])).
% 2.61/1.00  
% 2.61/1.00  fof(f102,plain,(
% 2.61/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.61/1.00    inference(equality_resolution,[],[f72])).
% 2.61/1.00  
% 2.61/1.00  fof(f10,axiom,(
% 2.61/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.61/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f30,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.61/1.00    inference(ennf_transformation,[],[f10])).
% 2.61/1.00  
% 2.61/1.00  fof(f31,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.61/1.00    inference(flattening,[],[f30])).
% 2.61/1.00  
% 2.61/1.00  fof(f71,plain,(
% 2.61/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f31])).
% 2.61/1.00  
% 2.61/1.00  fof(f100,plain,(
% 2.61/1.00    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.61/1.00    inference(equality_resolution,[],[f71])).
% 2.61/1.00  
% 2.61/1.00  fof(f5,axiom,(
% 2.61/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.61/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.00  
% 2.61/1.00  fof(f20,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.61/1.00    inference(ennf_transformation,[],[f5])).
% 2.61/1.00  
% 2.61/1.00  fof(f21,plain,(
% 2.61/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.61/1.00    inference(flattening,[],[f20])).
% 2.61/1.00  
% 2.61/1.00  fof(f62,plain,(
% 2.61/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f21])).
% 2.61/1.00  
% 2.61/1.00  fof(f96,plain,(
% 2.61/1.00    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK2,sK5,sK7)),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f73,plain,(
% 2.61/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.61/1.00    inference(cnf_transformation,[],[f44])).
% 2.61/1.00  
% 2.61/1.00  fof(f101,plain,(
% 2.61/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.61/1.00    inference(equality_resolution,[],[f73])).
% 2.61/1.00  
% 2.61/1.00  fof(f57,plain,(
% 2.61/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.61/1.00    inference(cnf_transformation,[],[f39])).
% 2.61/1.00  
% 2.61/1.00  fof(f98,plain,(
% 2.61/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.61/1.00    inference(equality_resolution,[],[f57])).
% 2.61/1.00  
% 2.61/1.00  fof(f93,plain,(
% 2.61/1.00    r2_hidden(sK7,sK6)),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f90,plain,(
% 2.61/1.00    m1_subset_1(sK7,u1_struct_0(sK4))),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f94,plain,(
% 2.61/1.00    r1_tarski(sK6,u1_struct_0(sK3))),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f92,plain,(
% 2.61/1.00    v3_pre_topc(sK6,sK4)),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  fof(f89,plain,(
% 2.61/1.00    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))),
% 2.61/1.00    inference(cnf_transformation,[],[f55])).
% 2.61/1.00  
% 2.61/1.00  cnf(c_8,plain,
% 2.61/1.00      ( m1_connsp_2(X0,X1,X2)
% 2.61/1.00      | ~ v3_pre_topc(X3,X1)
% 2.61/1.00      | ~ r2_hidden(X2,X3)
% 2.61/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.61/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.61/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.61/1.00      | ~ r1_tarski(X3,X0)
% 2.61/1.00      | v2_struct_0(X1)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(X1) ),
% 2.61/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_4055,plain,
% 2.61/1.00      ( m1_connsp_2(X0,sK4,X1)
% 2.61/1.00      | ~ v3_pre_topc(sK6,sK4)
% 2.61/1.00      | ~ r2_hidden(X1,sK6)
% 2.61/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.61/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.61/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.61/1.00      | ~ r1_tarski(sK6,X0)
% 2.61/1.00      | v2_struct_0(sK4)
% 2.61/1.00      | ~ l1_pre_topc(sK4)
% 2.61/1.00      | ~ v2_pre_topc(sK4) ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_5824,plain,
% 2.61/1.00      ( m1_connsp_2(X0,sK4,sK8)
% 2.61/1.00      | ~ v3_pre_topc(sK6,sK4)
% 2.61/1.00      | ~ r2_hidden(sK8,sK6)
% 2.61/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.61/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.61/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK4))
% 2.61/1.00      | ~ r1_tarski(sK6,X0)
% 2.61/1.00      | v2_struct_0(sK4)
% 2.61/1.00      | ~ l1_pre_topc(sK4)
% 2.61/1.00      | ~ v2_pre_topc(sK4) ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_4055]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_6854,plain,
% 2.61/1.00      ( m1_connsp_2(sK6,sK4,sK8)
% 2.61/1.00      | ~ v3_pre_topc(sK6,sK4)
% 2.61/1.00      | ~ r2_hidden(sK8,sK6)
% 2.61/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.61/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK4))
% 2.61/1.00      | ~ r1_tarski(sK6,sK6)
% 2.61/1.00      | v2_struct_0(sK4)
% 2.61/1.00      | ~ l1_pre_topc(sK4)
% 2.61/1.00      | ~ v2_pre_topc(sK4) ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_5824]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_32,negated_conjecture,
% 2.61/1.00      ( m1_pre_topc(sK4,sK1) ),
% 2.61/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_3001,plain,
% 2.61/1.00      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_28,negated_conjecture,
% 2.61/1.00      ( m1_pre_topc(sK3,sK4) ),
% 2.61/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_3003,plain,
% 2.61/1.00      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_14,plain,
% 2.61/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.61/1.00      | ~ m1_pre_topc(X3,X4)
% 2.61/1.00      | ~ m1_pre_topc(X3,X1)
% 2.61/1.00      | ~ m1_pre_topc(X1,X4)
% 2.61/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.61/1.00      | ~ v1_funct_1(X0)
% 2.61/1.00      | v2_struct_0(X4)
% 2.61/1.00      | v2_struct_0(X2)
% 2.61/1.00      | ~ l1_pre_topc(X4)
% 2.61/1.00      | ~ l1_pre_topc(X2)
% 2.61/1.00      | ~ v2_pre_topc(X4)
% 2.61/1.00      | ~ v2_pre_topc(X2)
% 2.61/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.61/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_30,negated_conjecture,
% 2.61/1.00      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 2.61/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_929,plain,
% 2.61/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.61/1.00      | ~ m1_pre_topc(X0,X2)
% 2.61/1.00      | ~ m1_pre_topc(X1,X2)
% 2.61/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 2.61/1.00      | ~ v1_funct_1(X3)
% 2.61/1.00      | v2_struct_0(X4)
% 2.61/1.00      | v2_struct_0(X2)
% 2.61/1.00      | ~ l1_pre_topc(X4)
% 2.61/1.00      | ~ l1_pre_topc(X2)
% 2.61/1.00      | ~ v2_pre_topc(X4)
% 2.61/1.00      | ~ v2_pre_topc(X2)
% 2.61/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
% 2.61/1.00      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(X4) != u1_struct_0(sK2)
% 2.61/1.00      | sK5 != X3 ),
% 2.61/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_30]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_930,plain,
% 2.61/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.61/1.00      | ~ m1_pre_topc(X0,X2)
% 2.61/1.00      | ~ m1_pre_topc(X1,X2)
% 2.61/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.61/1.00      | ~ v1_funct_1(sK5)
% 2.61/1.00      | v2_struct_0(X2)
% 2.61/1.00      | v2_struct_0(X3)
% 2.61/1.00      | ~ l1_pre_topc(X2)
% 2.61/1.00      | ~ l1_pre_topc(X3)
% 2.61/1.00      | ~ v2_pre_topc(X2)
% 2.61/1.00      | ~ v2_pre_topc(X3)
% 2.61/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 2.61/1.00      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(X3) != u1_struct_0(sK2) ),
% 2.61/1.00      inference(unflattening,[status(thm)],[c_929]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_31,negated_conjecture,
% 2.61/1.00      ( v1_funct_1(sK5) ),
% 2.61/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_934,plain,
% 2.61/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.61/1.00      | ~ m1_pre_topc(X1,X2)
% 2.61/1.00      | ~ m1_pre_topc(X0,X2)
% 2.61/1.00      | ~ m1_pre_topc(X0,X1)
% 2.61/1.00      | v2_struct_0(X2)
% 2.61/1.00      | v2_struct_0(X3)
% 2.61/1.00      | ~ l1_pre_topc(X2)
% 2.61/1.00      | ~ l1_pre_topc(X3)
% 2.61/1.00      | ~ v2_pre_topc(X2)
% 2.61/1.00      | ~ v2_pre_topc(X3)
% 2.61/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 2.61/1.00      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(X3) != u1_struct_0(sK2) ),
% 2.61/1.00      inference(global_propositional_subsumption,
% 2.61/1.00                [status(thm)],
% 2.61/1.00                [c_930,c_31]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_935,plain,
% 2.61/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.61/1.00      | ~ m1_pre_topc(X0,X2)
% 2.61/1.00      | ~ m1_pre_topc(X1,X2)
% 2.61/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.61/1.00      | v2_struct_0(X2)
% 2.61/1.00      | v2_struct_0(X3)
% 2.61/1.00      | ~ l1_pre_topc(X2)
% 2.61/1.00      | ~ l1_pre_topc(X3)
% 2.61/1.00      | ~ v2_pre_topc(X2)
% 2.61/1.00      | ~ v2_pre_topc(X3)
% 2.61/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 2.61/1.00      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(X3) != u1_struct_0(sK2) ),
% 2.61/1.00      inference(renaming,[status(thm)],[c_934]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_18,plain,
% 2.61/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.61/1.00      | ~ m1_pre_topc(X2,X0)
% 2.61/1.00      | m1_pre_topc(X2,X1)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(X1) ),
% 2.61/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_966,plain,
% 2.61/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.61/1.00      | ~ m1_pre_topc(X1,X2)
% 2.61/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.61/1.00      | v2_struct_0(X2)
% 2.61/1.00      | v2_struct_0(X3)
% 2.61/1.00      | ~ l1_pre_topc(X2)
% 2.61/1.00      | ~ l1_pre_topc(X3)
% 2.61/1.00      | ~ v2_pre_topc(X2)
% 2.61/1.00      | ~ v2_pre_topc(X3)
% 2.61/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 2.61/1.00      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(X3) != u1_struct_0(sK2) ),
% 2.61/1.00      inference(forward_subsumption_resolution,
% 2.61/1.00                [status(thm)],
% 2.61/1.00                [c_935,c_18]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_2985,plain,
% 2.61/1.00      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK5)
% 2.61/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.61/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 2.61/1.00      | m1_pre_topc(X0,X3) != iProver_top
% 2.61/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.61/1.00      | v2_struct_0(X3) = iProver_top
% 2.61/1.00      | v2_struct_0(X1) = iProver_top
% 2.61/1.00      | l1_pre_topc(X3) != iProver_top
% 2.61/1.00      | l1_pre_topc(X1) != iProver_top
% 2.61/1.00      | v2_pre_topc(X3) != iProver_top
% 2.61/1.00      | v2_pre_topc(X1) != iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_966]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_3885,plain,
% 2.61/1.00      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k3_tmap_1(X2,X0,sK4,X1,sK5)
% 2.61/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.61/1.00      | m1_pre_topc(X1,sK4) != iProver_top
% 2.61/1.00      | m1_pre_topc(sK4,X2) != iProver_top
% 2.61/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.61/1.00      | v2_struct_0(X0) = iProver_top
% 2.61/1.00      | v2_struct_0(X2) = iProver_top
% 2.61/1.00      | l1_pre_topc(X0) != iProver_top
% 2.61/1.00      | l1_pre_topc(X2) != iProver_top
% 2.61/1.00      | v2_pre_topc(X0) != iProver_top
% 2.61/1.00      | v2_pre_topc(X2) != iProver_top ),
% 2.61/1.00      inference(equality_resolution,[status(thm)],[c_2985]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_6041,plain,
% 2.61/1.00      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK4,X0,sK5)
% 2.61/1.00      | m1_pre_topc(X0,sK4) != iProver_top
% 2.61/1.00      | m1_pre_topc(sK4,X1) != iProver_top
% 2.61/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.61/1.00      | v2_struct_0(X1) = iProver_top
% 2.61/1.00      | v2_struct_0(sK2) = iProver_top
% 2.61/1.00      | l1_pre_topc(X1) != iProver_top
% 2.61/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.61/1.00      | v2_pre_topc(X1) != iProver_top
% 2.61/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 2.61/1.00      inference(equality_resolution,[status(thm)],[c_3885]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_38,negated_conjecture,
% 2.61/1.00      ( ~ v2_struct_0(sK2) ),
% 2.61/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_45,plain,
% 2.61/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_37,negated_conjecture,
% 2.61/1.00      ( v2_pre_topc(sK2) ),
% 2.61/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_46,plain,
% 2.61/1.00      ( v2_pre_topc(sK2) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_36,negated_conjecture,
% 2.61/1.00      ( l1_pre_topc(sK2) ),
% 2.61/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_47,plain,
% 2.61/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_29,negated_conjecture,
% 2.61/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 2.61/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_54,plain,
% 2.61/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_6681,plain,
% 2.61/1.00      ( v2_pre_topc(X1) != iProver_top
% 2.61/1.00      | v2_struct_0(X1) = iProver_top
% 2.61/1.00      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK4,X0,sK5)
% 2.61/1.00      | m1_pre_topc(X0,sK4) != iProver_top
% 2.61/1.00      | m1_pre_topc(sK4,X1) != iProver_top
% 2.61/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.61/1.00      inference(global_propositional_subsumption,
% 2.61/1.00                [status(thm)],
% 2.61/1.00                [c_6041,c_45,c_46,c_47,c_54]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_6682,plain,
% 2.61/1.00      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK4,X0,sK5)
% 2.61/1.00      | m1_pre_topc(X0,sK4) != iProver_top
% 2.61/1.00      | m1_pre_topc(sK4,X1) != iProver_top
% 2.61/1.00      | v2_struct_0(X1) = iProver_top
% 2.61/1.00      | l1_pre_topc(X1) != iProver_top
% 2.61/1.00      | v2_pre_topc(X1) != iProver_top ),
% 2.61/1.00      inference(renaming,[status(thm)],[c_6681]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_6693,plain,
% 2.61/1.00      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k3_tmap_1(X0,sK2,sK4,sK3,sK5)
% 2.61/1.00      | m1_pre_topc(sK4,X0) != iProver_top
% 2.61/1.00      | v2_struct_0(X0) = iProver_top
% 2.61/1.00      | l1_pre_topc(X0) != iProver_top
% 2.61/1.00      | v2_pre_topc(X0) != iProver_top ),
% 2.61/1.00      inference(superposition,[status(thm)],[c_3003,c_6682]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_13,plain,
% 2.61/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.61/1.00      | ~ m1_pre_topc(X3,X1)
% 2.61/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.61/1.00      | ~ v1_funct_1(X0)
% 2.61/1.00      | v2_struct_0(X1)
% 2.61/1.00      | v2_struct_0(X2)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ l1_pre_topc(X2)
% 2.61/1.00      | ~ v2_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(X2)
% 2.61/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.61/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_980,plain,
% 2.61/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.61/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.61/1.00      | ~ v1_funct_1(X2)
% 2.61/1.00      | v2_struct_0(X1)
% 2.61/1.00      | v2_struct_0(X3)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ l1_pre_topc(X3)
% 2.61/1.00      | ~ v2_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(X3)
% 2.61/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 2.61/1.00      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(X3) != u1_struct_0(sK2)
% 2.61/1.00      | sK5 != X2 ),
% 2.61/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_30]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_981,plain,
% 2.61/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.61/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.61/1.00      | ~ v1_funct_1(sK5)
% 2.61/1.00      | v2_struct_0(X1)
% 2.61/1.00      | v2_struct_0(X2)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ l1_pre_topc(X2)
% 2.61/1.00      | ~ v2_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(X2)
% 2.61/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
% 2.61/1.00      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(X2) != u1_struct_0(sK2) ),
% 2.61/1.00      inference(unflattening,[status(thm)],[c_980]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_985,plain,
% 2.61/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.61/1.00      | ~ m1_pre_topc(X0,X1)
% 2.61/1.00      | v2_struct_0(X1)
% 2.61/1.00      | v2_struct_0(X2)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ l1_pre_topc(X2)
% 2.61/1.00      | ~ v2_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(X2)
% 2.61/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
% 2.61/1.00      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(X2) != u1_struct_0(sK2) ),
% 2.61/1.00      inference(global_propositional_subsumption,
% 2.61/1.00                [status(thm)],
% 2.61/1.00                [c_981,c_31]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_986,plain,
% 2.61/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.61/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.61/1.00      | v2_struct_0(X1)
% 2.61/1.00      | v2_struct_0(X2)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ l1_pre_topc(X2)
% 2.61/1.00      | ~ v2_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(X2)
% 2.61/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
% 2.61/1.00      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(X2) != u1_struct_0(sK2) ),
% 2.61/1.00      inference(renaming,[status(thm)],[c_985]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_2984,plain,
% 2.61/1.00      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK5,X2)
% 2.61/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.61/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 2.61/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.61/1.00      | v2_struct_0(X0) = iProver_top
% 2.61/1.00      | v2_struct_0(X1) = iProver_top
% 2.61/1.00      | l1_pre_topc(X0) != iProver_top
% 2.61/1.00      | l1_pre_topc(X1) != iProver_top
% 2.61/1.00      | v2_pre_topc(X0) != iProver_top
% 2.61/1.00      | v2_pre_topc(X1) != iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_986]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_3605,plain,
% 2.61/1.00      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
% 2.61/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.61/1.00      | m1_pre_topc(X1,sK4) != iProver_top
% 2.61/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.61/1.00      | v2_struct_0(X0) = iProver_top
% 2.61/1.00      | v2_struct_0(sK4) = iProver_top
% 2.61/1.00      | l1_pre_topc(X0) != iProver_top
% 2.61/1.00      | l1_pre_topc(sK4) != iProver_top
% 2.61/1.00      | v2_pre_topc(X0) != iProver_top
% 2.61/1.00      | v2_pre_topc(sK4) != iProver_top ),
% 2.61/1.00      inference(equality_resolution,[status(thm)],[c_2984]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_40,negated_conjecture,
% 2.61/1.00      ( v2_pre_topc(sK1) ),
% 2.61/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_43,plain,
% 2.61/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_39,negated_conjecture,
% 2.61/1.00      ( l1_pre_topc(sK1) ),
% 2.61/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_44,plain,
% 2.61/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_33,negated_conjecture,
% 2.61/1.00      ( ~ v2_struct_0(sK4) ),
% 2.61/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_50,plain,
% 2.61/1.00      ( v2_struct_0(sK4) != iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_51,plain,
% 2.61/1.00      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_5,plain,
% 2.61/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.61/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_3446,plain,
% 2.61/1.00      ( ~ m1_pre_topc(X0,sK1) | l1_pre_topc(X0) | ~ l1_pre_topc(sK1) ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_3447,plain,
% 2.61/1.00      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.61/1.00      | l1_pre_topc(X0) = iProver_top
% 2.61/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_3446]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_3449,plain,
% 2.61/1.00      ( m1_pre_topc(sK4,sK1) != iProver_top
% 2.61/1.00      | l1_pre_topc(sK4) = iProver_top
% 2.61/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_3447]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_4,plain,
% 2.61/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(X1)
% 2.61/1.00      | v2_pre_topc(X0) ),
% 2.61/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_3480,plain,
% 2.61/1.00      ( ~ m1_pre_topc(X0,sK1)
% 2.61/1.00      | ~ l1_pre_topc(sK1)
% 2.61/1.00      | v2_pre_topc(X0)
% 2.61/1.00      | ~ v2_pre_topc(sK1) ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_3481,plain,
% 2.61/1.00      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.61/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.61/1.00      | v2_pre_topc(X0) = iProver_top
% 2.61/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_3480]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_3483,plain,
% 2.61/1.00      ( m1_pre_topc(sK4,sK1) != iProver_top
% 2.61/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.61/1.00      | v2_pre_topc(sK4) = iProver_top
% 2.61/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_3481]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_5398,plain,
% 2.61/1.00      ( v2_pre_topc(X0) != iProver_top
% 2.61/1.00      | v2_struct_0(X0) = iProver_top
% 2.61/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.61/1.00      | m1_pre_topc(X1,sK4) != iProver_top
% 2.61/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.61/1.00      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
% 2.61/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.61/1.00      inference(global_propositional_subsumption,
% 2.61/1.00                [status(thm)],
% 2.61/1.00                [c_3605,c_43,c_44,c_50,c_51,c_3449,c_3483]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_5399,plain,
% 2.61/1.00      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
% 2.61/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.61/1.00      | m1_pre_topc(X1,sK4) != iProver_top
% 2.61/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.61/1.00      | v2_struct_0(X0) = iProver_top
% 2.61/1.00      | l1_pre_topc(X0) != iProver_top
% 2.61/1.00      | v2_pre_topc(X0) != iProver_top ),
% 2.61/1.00      inference(renaming,[status(thm)],[c_5398]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_5409,plain,
% 2.61/1.00      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK2,sK5,X0)
% 2.61/1.00      | m1_pre_topc(X0,sK4) != iProver_top
% 2.61/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.61/1.00      | v2_struct_0(sK2) = iProver_top
% 2.61/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.61/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 2.61/1.00      inference(equality_resolution,[status(thm)],[c_5399]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_5950,plain,
% 2.61/1.00      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK2,sK5,X0)
% 2.61/1.00      | m1_pre_topc(X0,sK4) != iProver_top ),
% 2.61/1.00      inference(global_propositional_subsumption,
% 2.61/1.00                [status(thm)],
% 2.61/1.00                [c_5409,c_45,c_46,c_47,c_54]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_5958,plain,
% 2.61/1.00      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK2,sK5,sK3) ),
% 2.61/1.00      inference(superposition,[status(thm)],[c_3003,c_5950]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_6694,plain,
% 2.61/1.00      ( k3_tmap_1(X0,sK2,sK4,sK3,sK5) = k2_tmap_1(sK4,sK2,sK5,sK3)
% 2.61/1.00      | m1_pre_topc(sK4,X0) != iProver_top
% 2.61/1.00      | v2_struct_0(X0) = iProver_top
% 2.61/1.00      | l1_pre_topc(X0) != iProver_top
% 2.61/1.00      | v2_pre_topc(X0) != iProver_top ),
% 2.61/1.00      inference(light_normalisation,[status(thm)],[c_6693,c_5958]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_6758,plain,
% 2.61/1.00      ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_tmap_1(sK4,sK2,sK5,sK3)
% 2.61/1.00      | v2_struct_0(sK1) = iProver_top
% 2.61/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.61/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.61/1.00      inference(superposition,[status(thm)],[c_3001,c_6694]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_41,negated_conjecture,
% 2.61/1.00      ( ~ v2_struct_0(sK1) ),
% 2.61/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_42,plain,
% 2.61/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_6761,plain,
% 2.61/1.00      ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_tmap_1(sK4,sK2,sK5,sK3) ),
% 2.61/1.00      inference(global_propositional_subsumption,
% 2.61/1.00                [status(thm)],
% 2.61/1.00                [c_6758,c_42,c_43,c_44]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_19,negated_conjecture,
% 2.61/1.00      ( ~ r1_tmap_1(sK4,sK2,sK5,sK7)
% 2.61/1.00      | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
% 2.61/1.00      inference(cnf_transformation,[],[f97]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_3011,plain,
% 2.61/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
% 2.61/1.00      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_21,negated_conjecture,
% 2.61/1.00      ( sK7 = sK8 ),
% 2.61/1.00      inference(cnf_transformation,[],[f95]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_3086,plain,
% 2.61/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
% 2.61/1.00      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top ),
% 2.61/1.00      inference(light_normalisation,[status(thm)],[c_3011,c_21]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_6765,plain,
% 2.61/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
% 2.61/1.00      | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8) != iProver_top ),
% 2.61/1.00      inference(demodulation,[status(thm)],[c_6761,c_3086]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_35,negated_conjecture,
% 2.61/1.00      ( ~ v2_struct_0(sK3) ),
% 2.61/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_48,plain,
% 2.61/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_55,plain,
% 2.61/1.00      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_25,negated_conjecture,
% 2.61/1.00      ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
% 2.61/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_58,plain,
% 2.61/1.00      ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_2,plain,
% 2.61/1.00      ( r1_tarski(X0,X0) ),
% 2.61/1.00      inference(cnf_transformation,[],[f99]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_105,plain,
% 2.61/1.00      ( r1_tarski(sK4,sK4) ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_0,plain,
% 2.61/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.61/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_109,plain,
% 2.61/1.00      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_2077,plain,
% 2.61/1.00      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 2.61/1.00      theory(equality) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_2092,plain,
% 2.61/1.00      ( u1_struct_0(sK4) = u1_struct_0(sK4) | sK4 != sK4 ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_2077]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_2068,plain,( X0 = X0 ),theory(equality) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_3804,plain,
% 2.61/1.00      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_2068]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_17,plain,
% 2.61/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.61/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.61/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.61/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 2.61/1.00      | ~ m1_pre_topc(X4,X0)
% 2.61/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.61/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.61/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.61/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.61/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.61/1.00      | ~ v1_funct_1(X2)
% 2.61/1.00      | v2_struct_0(X1)
% 2.61/1.00      | v2_struct_0(X0)
% 2.61/1.00      | v2_struct_0(X4)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ l1_pre_topc(X0)
% 2.61/1.00      | ~ v2_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(X0) ),
% 2.61/1.00      inference(cnf_transformation,[],[f102]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_15,plain,
% 2.61/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.61/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.61/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.61/1.00      | ~ m1_pre_topc(X4,X0)
% 2.61/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.61/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.61/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.61/1.00      | ~ v1_funct_1(X2)
% 2.61/1.00      | v2_struct_0(X1)
% 2.61/1.00      | v2_struct_0(X0)
% 2.61/1.00      | v2_struct_0(X4)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ l1_pre_topc(X0)
% 2.61/1.00      | ~ v2_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(X0) ),
% 2.61/1.00      inference(cnf_transformation,[],[f100]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_217,plain,
% 2.61/1.00      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.61/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.61/1.00      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.61/1.00      | ~ m1_pre_topc(X4,X0)
% 2.61/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.61/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.61/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.61/1.00      | ~ v1_funct_1(X2)
% 2.61/1.00      | v2_struct_0(X1)
% 2.61/1.00      | v2_struct_0(X0)
% 2.61/1.00      | v2_struct_0(X4)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ l1_pre_topc(X0)
% 2.61/1.00      | ~ v2_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(X0) ),
% 2.61/1.00      inference(global_propositional_subsumption,
% 2.61/1.00                [status(thm)],
% 2.61/1.00                [c_17,c_15]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_218,plain,
% 2.61/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.61/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.61/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.61/1.00      | ~ m1_pre_topc(X4,X0)
% 2.61/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.61/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.61/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.61/1.00      | ~ v1_funct_1(X2)
% 2.61/1.00      | v2_struct_0(X0)
% 2.61/1.00      | v2_struct_0(X1)
% 2.61/1.00      | v2_struct_0(X4)
% 2.61/1.00      | ~ l1_pre_topc(X0)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(X0)
% 2.61/1.00      | ~ v2_pre_topc(X1) ),
% 2.61/1.00      inference(renaming,[status(thm)],[c_217]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_757,plain,
% 2.61/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.61/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.61/1.00      | ~ m1_pre_topc(X4,X0)
% 2.61/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.61/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.61/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.61/1.00      | ~ v1_funct_1(X2)
% 2.61/1.00      | v2_struct_0(X0)
% 2.61/1.00      | v2_struct_0(X1)
% 2.61/1.00      | v2_struct_0(X4)
% 2.61/1.00      | ~ l1_pre_topc(X0)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(X0)
% 2.61/1.00      | ~ v2_pre_topc(X1)
% 2.61/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.61/1.00      | sK5 != X2 ),
% 2.61/1.00      inference(resolution_lifted,[status(thm)],[c_218,c_30]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_758,plain,
% 2.61/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.61/1.00      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.61/1.00      | ~ m1_pre_topc(X0,X2)
% 2.61/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.61/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.61/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.61/1.00      | ~ v1_funct_1(sK5)
% 2.61/1.00      | v2_struct_0(X2)
% 2.61/1.00      | v2_struct_0(X1)
% 2.61/1.00      | v2_struct_0(X0)
% 2.61/1.00      | ~ l1_pre_topc(X2)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(X2)
% 2.61/1.00      | ~ v2_pre_topc(X1)
% 2.61/1.00      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.61/1.00      inference(unflattening,[status(thm)],[c_757]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_762,plain,
% 2.61/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.61/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.61/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.61/1.00      | ~ m1_pre_topc(X0,X2)
% 2.61/1.00      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.61/1.00      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.61/1.00      | v2_struct_0(X2)
% 2.61/1.00      | v2_struct_0(X1)
% 2.61/1.00      | v2_struct_0(X0)
% 2.61/1.00      | ~ l1_pre_topc(X2)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(X2)
% 2.61/1.00      | ~ v2_pre_topc(X1)
% 2.61/1.00      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.61/1.00      inference(global_propositional_subsumption,
% 2.61/1.00                [status(thm)],
% 2.61/1.00                [c_758,c_31]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_763,plain,
% 2.61/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.61/1.00      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.61/1.00      | ~ m1_pre_topc(X0,X2)
% 2.61/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.61/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.61/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.61/1.00      | v2_struct_0(X0)
% 2.61/1.00      | v2_struct_0(X1)
% 2.61/1.00      | v2_struct_0(X2)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ l1_pre_topc(X2)
% 2.61/1.00      | ~ v2_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(X2)
% 2.61/1.00      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.61/1.00      inference(renaming,[status(thm)],[c_762]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_6,plain,
% 2.61/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.61/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.61/1.00      | m1_subset_1(X2,u1_struct_0(X1))
% 2.61/1.00      | v2_struct_0(X1)
% 2.61/1.00      | v2_struct_0(X0)
% 2.61/1.00      | ~ l1_pre_topc(X1) ),
% 2.61/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_798,plain,
% 2.61/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.61/1.00      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.61/1.00      | ~ m1_pre_topc(X0,X2)
% 2.61/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.61/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.61/1.00      | v2_struct_0(X0)
% 2.61/1.00      | v2_struct_0(X1)
% 2.61/1.00      | v2_struct_0(X2)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ l1_pre_topc(X2)
% 2.61/1.00      | ~ v2_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(X2)
% 2.61/1.00      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.61/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_763,c_6]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_3421,plain,
% 2.61/1.00      ( r1_tmap_1(X0,sK2,k2_tmap_1(X1,sK2,sK5,X0),X2)
% 2.61/1.00      | ~ r1_tmap_1(X1,sK2,sK5,X2)
% 2.61/1.00      | ~ m1_pre_topc(X0,X1)
% 2.61/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.61/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
% 2.61/1.00      | v2_struct_0(X0)
% 2.61/1.00      | v2_struct_0(X1)
% 2.61/1.00      | v2_struct_0(sK2)
% 2.61/1.00      | ~ l1_pre_topc(X1)
% 2.61/1.00      | ~ l1_pre_topc(sK2)
% 2.61/1.00      | ~ v2_pre_topc(X1)
% 2.61/1.00      | ~ v2_pre_topc(sK2)
% 2.61/1.00      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_798]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_4334,plain,
% 2.61/1.00      ( ~ r1_tmap_1(sK4,sK2,sK5,X0)
% 2.61/1.00      | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),X0)
% 2.61/1.00      | ~ m1_pre_topc(sK3,sK4)
% 2.61/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.61/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 2.61/1.00      | v2_struct_0(sK4)
% 2.61/1.00      | v2_struct_0(sK2)
% 2.61/1.00      | v2_struct_0(sK3)
% 2.61/1.00      | ~ l1_pre_topc(sK4)
% 2.61/1.00      | ~ l1_pre_topc(sK2)
% 2.61/1.00      | ~ v2_pre_topc(sK4)
% 2.61/1.00      | ~ v2_pre_topc(sK2)
% 2.61/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_3421]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_4468,plain,
% 2.61/1.00      ( ~ r1_tmap_1(sK4,sK2,sK5,sK8)
% 2.61/1.00      | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8)
% 2.61/1.00      | ~ m1_pre_topc(sK3,sK4)
% 2.61/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK3))
% 2.61/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 2.61/1.00      | v2_struct_0(sK4)
% 2.61/1.00      | v2_struct_0(sK2)
% 2.61/1.00      | v2_struct_0(sK3)
% 2.61/1.00      | ~ l1_pre_topc(sK4)
% 2.61/1.00      | ~ l1_pre_topc(sK2)
% 2.61/1.00      | ~ v2_pre_topc(sK4)
% 2.61/1.00      | ~ v2_pre_topc(sK2)
% 2.61/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.61/1.00      inference(instantiation,[status(thm)],[c_4334]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_4469,plain,
% 2.61/1.00      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.61/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.61/1.00      | r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
% 2.61/1.00      | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8) = iProver_top
% 2.61/1.00      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.61/1.00      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 2.61/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.61/1.00      | v2_struct_0(sK4) = iProver_top
% 2.61/1.00      | v2_struct_0(sK2) = iProver_top
% 2.61/1.00      | v2_struct_0(sK3) = iProver_top
% 2.61/1.00      | l1_pre_topc(sK4) != iProver_top
% 2.61/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.61/1.00      | v2_pre_topc(sK4) != iProver_top
% 2.61/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 2.61/1.00      inference(predicate_to_equality,[status(thm)],[c_4468]) ).
% 2.61/1.00  
% 2.61/1.00  cnf(c_6831,plain,
% 2.61/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top ),
% 2.61/1.00      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_6765,c_43,c_44,c_45,c_46,c_47,c_48,c_50,c_51,c_54,
% 2.61/1.01                 c_55,c_58,c_105,c_109,c_2092,c_3449,c_3483,c_3804,
% 2.61/1.01                 c_4469]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_6833,plain,
% 2.61/1.01      ( ~ r1_tmap_1(sK4,sK2,sK5,sK8) ),
% 2.61/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_6831]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_20,negated_conjecture,
% 2.61/1.01      ( r1_tmap_1(sK4,sK2,sK5,sK7)
% 2.61/1.01      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
% 2.61/1.01      inference(cnf_transformation,[],[f96]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3010,plain,
% 2.61/1.01      ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
% 2.61/1.01      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) = iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3075,plain,
% 2.61/1.01      ( r1_tmap_1(sK4,sK2,sK5,sK8) = iProver_top
% 2.61/1.01      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) = iProver_top ),
% 2.61/1.01      inference(light_normalisation,[status(thm)],[c_3010,c_21]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_6764,plain,
% 2.61/1.01      ( r1_tmap_1(sK4,sK2,sK5,sK8) = iProver_top
% 2.61/1.01      | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8) = iProver_top ),
% 2.61/1.01      inference(demodulation,[status(thm)],[c_6761,c_3075]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_6774,plain,
% 2.61/1.01      ( r1_tmap_1(sK4,sK2,sK5,sK8)
% 2.61/1.01      | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8) ),
% 2.61/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_6764]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_16,plain,
% 2.61/1.01      ( r1_tmap_1(X0,X1,X2,X3)
% 2.61/1.01      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.61/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.61/1.01      | ~ m1_connsp_2(X5,X0,X3)
% 2.61/1.01      | ~ m1_pre_topc(X4,X0)
% 2.61/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.61/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.61/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.61/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.61/1.01      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.61/1.01      | ~ v1_funct_1(X2)
% 2.61/1.01      | v2_struct_0(X1)
% 2.61/1.01      | v2_struct_0(X0)
% 2.61/1.01      | v2_struct_0(X4)
% 2.61/1.01      | ~ l1_pre_topc(X1)
% 2.61/1.01      | ~ l1_pre_topc(X0)
% 2.61/1.01      | ~ v2_pre_topc(X1)
% 2.61/1.01      | ~ v2_pre_topc(X0) ),
% 2.61/1.01      inference(cnf_transformation,[],[f101]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_814,plain,
% 2.61/1.01      ( r1_tmap_1(X0,X1,X2,X3)
% 2.61/1.01      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.61/1.01      | ~ m1_connsp_2(X5,X0,X3)
% 2.61/1.01      | ~ m1_pre_topc(X4,X0)
% 2.61/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.61/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.61/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.61/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.61/1.01      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.61/1.01      | ~ v1_funct_1(X2)
% 2.61/1.01      | v2_struct_0(X0)
% 2.61/1.01      | v2_struct_0(X1)
% 2.61/1.01      | v2_struct_0(X4)
% 2.61/1.01      | ~ l1_pre_topc(X0)
% 2.61/1.01      | ~ l1_pre_topc(X1)
% 2.61/1.01      | ~ v2_pre_topc(X0)
% 2.61/1.01      | ~ v2_pre_topc(X1)
% 2.61/1.01      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.61/1.01      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.61/1.01      | sK5 != X2 ),
% 2.61/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_30]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_815,plain,
% 2.61/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.61/1.01      | r1_tmap_1(X2,X1,sK5,X3)
% 2.61/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.61/1.01      | ~ m1_pre_topc(X0,X2)
% 2.61/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.61/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.61/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.61/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.61/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.61/1.01      | ~ v1_funct_1(sK5)
% 2.61/1.01      | v2_struct_0(X2)
% 2.61/1.01      | v2_struct_0(X1)
% 2.61/1.01      | v2_struct_0(X0)
% 2.61/1.01      | ~ l1_pre_topc(X2)
% 2.61/1.01      | ~ l1_pre_topc(X1)
% 2.61/1.01      | ~ v2_pre_topc(X2)
% 2.61/1.01      | ~ v2_pre_topc(X1)
% 2.61/1.01      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.61/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.61/1.01      inference(unflattening,[status(thm)],[c_814]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_819,plain,
% 2.61/1.01      ( ~ r1_tarski(X4,u1_struct_0(X0))
% 2.61/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.61/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.61/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.61/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.61/1.01      | ~ m1_pre_topc(X0,X2)
% 2.61/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.61/1.01      | r1_tmap_1(X2,X1,sK5,X3)
% 2.61/1.01      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.61/1.01      | v2_struct_0(X2)
% 2.61/1.01      | v2_struct_0(X1)
% 2.61/1.01      | v2_struct_0(X0)
% 2.61/1.01      | ~ l1_pre_topc(X2)
% 2.61/1.01      | ~ l1_pre_topc(X1)
% 2.61/1.01      | ~ v2_pre_topc(X2)
% 2.61/1.01      | ~ v2_pre_topc(X1)
% 2.61/1.01      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.61/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_815,c_31]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_820,plain,
% 2.61/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.61/1.01      | r1_tmap_1(X2,X1,sK5,X3)
% 2.61/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.61/1.01      | ~ m1_pre_topc(X0,X2)
% 2.61/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.61/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.61/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.61/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.61/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.61/1.01      | v2_struct_0(X0)
% 2.61/1.01      | v2_struct_0(X1)
% 2.61/1.01      | v2_struct_0(X2)
% 2.61/1.01      | ~ l1_pre_topc(X1)
% 2.61/1.01      | ~ l1_pre_topc(X2)
% 2.61/1.01      | ~ v2_pre_topc(X1)
% 2.61/1.01      | ~ v2_pre_topc(X2)
% 2.61/1.01      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.61/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.61/1.01      inference(renaming,[status(thm)],[c_819]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_861,plain,
% 2.61/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.61/1.01      | r1_tmap_1(X2,X1,sK5,X3)
% 2.61/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.61/1.01      | ~ m1_pre_topc(X0,X2)
% 2.61/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.61/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.61/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.61/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.61/1.01      | v2_struct_0(X0)
% 2.61/1.01      | v2_struct_0(X1)
% 2.61/1.01      | v2_struct_0(X2)
% 2.61/1.01      | ~ l1_pre_topc(X1)
% 2.61/1.01      | ~ l1_pre_topc(X2)
% 2.61/1.01      | ~ v2_pre_topc(X1)
% 2.61/1.01      | ~ v2_pre_topc(X2)
% 2.61/1.01      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.61/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.61/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_820,c_6]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3431,plain,
% 2.61/1.01      ( ~ r1_tmap_1(X0,sK2,k2_tmap_1(X1,sK2,sK5,X0),X2)
% 2.61/1.01      | r1_tmap_1(X1,sK2,sK5,X2)
% 2.61/1.01      | ~ m1_connsp_2(X3,X1,X2)
% 2.61/1.01      | ~ m1_pre_topc(X0,X1)
% 2.61/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.61/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.61/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
% 2.61/1.01      | ~ r1_tarski(X3,u1_struct_0(X0))
% 2.61/1.01      | v2_struct_0(X0)
% 2.61/1.01      | v2_struct_0(X1)
% 2.61/1.01      | v2_struct_0(sK2)
% 2.61/1.01      | ~ l1_pre_topc(X1)
% 2.61/1.01      | ~ l1_pre_topc(sK2)
% 2.61/1.01      | ~ v2_pre_topc(X1)
% 2.61/1.01      | ~ v2_pre_topc(sK2)
% 2.61/1.01      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.61/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_861]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_4352,plain,
% 2.61/1.01      ( r1_tmap_1(sK4,sK2,sK5,X0)
% 2.61/1.01      | ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),X0)
% 2.61/1.01      | ~ m1_connsp_2(X1,sK4,X0)
% 2.61/1.01      | ~ m1_pre_topc(sK3,sK4)
% 2.61/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.61/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.61/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 2.61/1.01      | ~ r1_tarski(X1,u1_struct_0(sK3))
% 2.61/1.01      | v2_struct_0(sK4)
% 2.61/1.01      | v2_struct_0(sK2)
% 2.61/1.01      | v2_struct_0(sK3)
% 2.61/1.01      | ~ l1_pre_topc(sK4)
% 2.61/1.01      | ~ l1_pre_topc(sK2)
% 2.61/1.01      | ~ v2_pre_topc(sK4)
% 2.61/1.01      | ~ v2_pre_topc(sK2)
% 2.61/1.01      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.61/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_3431]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_4531,plain,
% 2.61/1.01      ( r1_tmap_1(sK4,sK2,sK5,sK8)
% 2.61/1.01      | ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8)
% 2.61/1.01      | ~ m1_connsp_2(X0,sK4,sK8)
% 2.61/1.01      | ~ m1_pre_topc(sK3,sK4)
% 2.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.61/1.01      | ~ m1_subset_1(sK8,u1_struct_0(sK3))
% 2.61/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 2.61/1.01      | ~ r1_tarski(X0,u1_struct_0(sK3))
% 2.61/1.01      | v2_struct_0(sK4)
% 2.61/1.01      | v2_struct_0(sK2)
% 2.61/1.01      | v2_struct_0(sK3)
% 2.61/1.01      | ~ l1_pre_topc(sK4)
% 2.61/1.01      | ~ l1_pre_topc(sK2)
% 2.61/1.01      | ~ v2_pre_topc(sK4)
% 2.61/1.01      | ~ v2_pre_topc(sK2)
% 2.61/1.01      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.61/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_4352]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_5454,plain,
% 2.61/1.01      ( r1_tmap_1(sK4,sK2,sK5,sK8)
% 2.61/1.01      | ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8)
% 2.61/1.01      | ~ m1_connsp_2(sK6,sK4,sK8)
% 2.61/1.01      | ~ m1_pre_topc(sK3,sK4)
% 2.61/1.01      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.61/1.01      | ~ m1_subset_1(sK8,u1_struct_0(sK3))
% 2.61/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 2.61/1.01      | ~ r1_tarski(sK6,u1_struct_0(sK3))
% 2.61/1.01      | v2_struct_0(sK4)
% 2.61/1.01      | v2_struct_0(sK2)
% 2.61/1.01      | v2_struct_0(sK3)
% 2.61/1.01      | ~ l1_pre_topc(sK4)
% 2.61/1.01      | ~ l1_pre_topc(sK2)
% 2.61/1.01      | ~ v2_pre_topc(sK4)
% 2.61/1.01      | ~ v2_pre_topc(sK2)
% 2.61/1.01      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.61/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_4531]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1,plain,
% 2.61/1.01      ( r1_tarski(X0,X0) ),
% 2.61/1.01      inference(cnf_transformation,[],[f98]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_4455,plain,
% 2.61/1.01      ( r1_tarski(sK6,sK6) ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3482,plain,
% 2.61/1.01      ( ~ m1_pre_topc(sK4,sK1)
% 2.61/1.01      | ~ l1_pre_topc(sK1)
% 2.61/1.01      | v2_pre_topc(sK4)
% 2.61/1.01      | ~ v2_pre_topc(sK1) ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_3480]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3448,plain,
% 2.61/1.01      ( ~ m1_pre_topc(sK4,sK1) | l1_pre_topc(sK4) | ~ l1_pre_topc(sK1) ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_3446]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_23,negated_conjecture,
% 2.61/1.01      ( r2_hidden(sK7,sK6) ),
% 2.61/1.01      inference(cnf_transformation,[],[f93]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3008,plain,
% 2.61/1.01      ( r2_hidden(sK7,sK6) = iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3047,plain,
% 2.61/1.01      ( r2_hidden(sK8,sK6) = iProver_top ),
% 2.61/1.01      inference(light_normalisation,[status(thm)],[c_3008,c_21]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3315,plain,
% 2.61/1.01      ( r2_hidden(sK8,sK6) ),
% 2.61/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_3047]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_26,negated_conjecture,
% 2.61/1.01      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 2.61/1.01      inference(cnf_transformation,[],[f90]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3005,plain,
% 2.61/1.01      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3052,plain,
% 2.61/1.01      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 2.61/1.01      inference(light_normalisation,[status(thm)],[c_3005,c_21]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3313,plain,
% 2.61/1.01      ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
% 2.61/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_3052]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_22,negated_conjecture,
% 2.61/1.01      ( r1_tarski(sK6,u1_struct_0(sK3)) ),
% 2.61/1.01      inference(cnf_transformation,[],[f94]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_24,negated_conjecture,
% 2.61/1.01      ( v3_pre_topc(sK6,sK4) ),
% 2.61/1.01      inference(cnf_transformation,[],[f92]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_27,negated_conjecture,
% 2.61/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.61/1.01      inference(cnf_transformation,[],[f89]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(contradiction,plain,
% 2.61/1.01      ( $false ),
% 2.61/1.01      inference(minisat,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_6854,c_6833,c_6774,c_5454,c_4455,c_3804,c_3482,c_3448,
% 2.61/1.01                 c_3315,c_3313,c_2092,c_109,c_105,c_22,c_24,c_25,c_27,
% 2.61/1.01                 c_28,c_29,c_32,c_33,c_35,c_36,c_37,c_38,c_39,c_40]) ).
% 2.61/1.01  
% 2.61/1.01  
% 2.61/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.61/1.01  
% 2.61/1.01  ------                               Statistics
% 2.61/1.01  
% 2.61/1.01  ------ General
% 2.61/1.01  
% 2.61/1.01  abstr_ref_over_cycles:                  0
% 2.61/1.01  abstr_ref_under_cycles:                 0
% 2.61/1.01  gc_basic_clause_elim:                   0
% 2.61/1.01  forced_gc_time:                         0
% 2.61/1.01  parsing_time:                           0.017
% 2.61/1.01  unif_index_cands_time:                  0.
% 2.61/1.01  unif_index_add_time:                    0.
% 2.61/1.01  orderings_time:                         0.
% 2.61/1.01  out_proof_time:                         0.021
% 2.61/1.01  total_time:                             0.261
% 2.61/1.01  num_of_symbols:                         58
% 2.61/1.01  num_of_terms:                           3684
% 2.61/1.01  
% 2.61/1.01  ------ Preprocessing
% 2.61/1.01  
% 2.61/1.01  num_of_splits:                          0
% 2.61/1.01  num_of_split_atoms:                     0
% 2.61/1.01  num_of_reused_defs:                     0
% 2.61/1.01  num_eq_ax_congr_red:                    29
% 2.61/1.01  num_of_sem_filtered_clauses:            1
% 2.61/1.01  num_of_subtypes:                        0
% 2.61/1.01  monotx_restored_types:                  0
% 2.61/1.01  sat_num_of_epr_types:                   0
% 2.61/1.01  sat_num_of_non_cyclic_types:            0
% 2.61/1.01  sat_guarded_non_collapsed_types:        0
% 2.61/1.01  num_pure_diseq_elim:                    0
% 2.61/1.01  simp_replaced_by:                       0
% 2.61/1.01  res_preprocessed:                       190
% 2.61/1.01  prep_upred:                             0
% 2.61/1.01  prep_unflattend:                        35
% 2.61/1.01  smt_new_axioms:                         0
% 2.61/1.01  pred_elim_cands:                        10
% 2.61/1.01  pred_elim:                              2
% 2.61/1.01  pred_elim_cl:                           3
% 2.61/1.01  pred_elim_cycles:                       8
% 2.61/1.01  merged_defs:                            8
% 2.61/1.01  merged_defs_ncl:                        0
% 2.61/1.01  bin_hyper_res:                          8
% 2.61/1.01  prep_cycles:                            4
% 2.61/1.01  pred_elim_time:                         0.046
% 2.61/1.01  splitting_time:                         0.
% 2.61/1.01  sem_filter_time:                        0.
% 2.61/1.01  monotx_time:                            0.001
% 2.61/1.01  subtype_inf_time:                       0.
% 2.61/1.01  
% 2.61/1.01  ------ Problem properties
% 2.61/1.01  
% 2.61/1.01  clauses:                                38
% 2.61/1.01  conjectures:                            21
% 2.61/1.01  epr:                                    19
% 2.61/1.01  horn:                                   26
% 2.61/1.01  ground:                                 21
% 2.61/1.01  unary:                                  20
% 2.61/1.01  binary:                                 2
% 2.61/1.01  lits:                                   142
% 2.61/1.01  lits_eq:                                12
% 2.61/1.01  fd_pure:                                0
% 2.61/1.01  fd_pseudo:                              0
% 2.61/1.01  fd_cond:                                0
% 2.61/1.01  fd_pseudo_cond:                         1
% 2.61/1.01  ac_symbols:                             0
% 2.61/1.01  
% 2.61/1.01  ------ Propositional Solver
% 2.61/1.01  
% 2.61/1.01  prop_solver_calls:                      28
% 2.61/1.01  prop_fast_solver_calls:                 2521
% 2.61/1.01  smt_solver_calls:                       0
% 2.61/1.01  smt_fast_solver_calls:                  0
% 2.61/1.01  prop_num_of_clauses:                    1716
% 2.61/1.01  prop_preprocess_simplified:             6879
% 2.61/1.01  prop_fo_subsumed:                       107
% 2.61/1.01  prop_solver_time:                       0.
% 2.61/1.01  smt_solver_time:                        0.
% 2.61/1.01  smt_fast_solver_time:                   0.
% 2.61/1.01  prop_fast_solver_time:                  0.
% 2.61/1.01  prop_unsat_core_time:                   0.
% 2.61/1.01  
% 2.61/1.01  ------ QBF
% 2.61/1.01  
% 2.61/1.01  qbf_q_res:                              0
% 2.61/1.01  qbf_num_tautologies:                    0
% 2.61/1.01  qbf_prep_cycles:                        0
% 2.61/1.01  
% 2.61/1.01  ------ BMC1
% 2.61/1.01  
% 2.61/1.01  bmc1_current_bound:                     -1
% 2.61/1.01  bmc1_last_solved_bound:                 -1
% 2.61/1.01  bmc1_unsat_core_size:                   -1
% 2.61/1.01  bmc1_unsat_core_parents_size:           -1
% 2.61/1.01  bmc1_merge_next_fun:                    0
% 2.61/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.61/1.01  
% 2.61/1.01  ------ Instantiation
% 2.61/1.01  
% 2.61/1.01  inst_num_of_clauses:                    493
% 2.61/1.01  inst_num_in_passive:                    84
% 2.61/1.01  inst_num_in_active:                     374
% 2.61/1.01  inst_num_in_unprocessed:                34
% 2.61/1.01  inst_num_of_loops:                      412
% 2.61/1.01  inst_num_of_learning_restarts:          0
% 2.61/1.01  inst_num_moves_active_passive:          34
% 2.61/1.01  inst_lit_activity:                      0
% 2.61/1.01  inst_lit_activity_moves:                0
% 2.61/1.01  inst_num_tautologies:                   0
% 2.61/1.01  inst_num_prop_implied:                  0
% 2.61/1.01  inst_num_existing_simplified:           0
% 2.61/1.01  inst_num_eq_res_simplified:             0
% 2.61/1.01  inst_num_child_elim:                    0
% 2.61/1.01  inst_num_of_dismatching_blockings:      56
% 2.61/1.01  inst_num_of_non_proper_insts:           616
% 2.61/1.01  inst_num_of_duplicates:                 0
% 2.61/1.01  inst_inst_num_from_inst_to_res:         0
% 2.61/1.01  inst_dismatching_checking_time:         0.
% 2.61/1.01  
% 2.61/1.01  ------ Resolution
% 2.61/1.01  
% 2.61/1.01  res_num_of_clauses:                     0
% 2.61/1.01  res_num_in_passive:                     0
% 2.61/1.01  res_num_in_active:                      0
% 2.61/1.01  res_num_of_loops:                       194
% 2.61/1.01  res_forward_subset_subsumed:            91
% 2.61/1.01  res_backward_subset_subsumed:           0
% 2.61/1.01  res_forward_subsumed:                   0
% 2.61/1.01  res_backward_subsumed:                  0
% 2.61/1.01  res_forward_subsumption_resolution:     10
% 2.61/1.01  res_backward_subsumption_resolution:    0
% 2.61/1.01  res_clause_to_clause_subsumption:       481
% 2.61/1.01  res_orphan_elimination:                 0
% 2.61/1.01  res_tautology_del:                      69
% 2.61/1.01  res_num_eq_res_simplified:              0
% 2.61/1.01  res_num_sel_changes:                    0
% 2.61/1.01  res_moves_from_active_to_pass:          0
% 2.61/1.01  
% 2.61/1.01  ------ Superposition
% 2.61/1.01  
% 2.61/1.01  sup_time_total:                         0.
% 2.61/1.01  sup_time_generating:                    0.
% 2.61/1.01  sup_time_sim_full:                      0.
% 2.61/1.01  sup_time_sim_immed:                     0.
% 2.61/1.01  
% 2.61/1.01  sup_num_of_clauses:                     84
% 2.61/1.01  sup_num_in_active:                      80
% 2.61/1.01  sup_num_in_passive:                     4
% 2.61/1.01  sup_num_of_loops:                       82
% 2.61/1.01  sup_fw_superposition:                   44
% 2.61/1.01  sup_bw_superposition:                   15
% 2.61/1.01  sup_immediate_simplified:               16
% 2.61/1.01  sup_given_eliminated:                   0
% 2.61/1.01  comparisons_done:                       0
% 2.61/1.01  comparisons_avoided:                    0
% 2.61/1.01  
% 2.61/1.01  ------ Simplifications
% 2.61/1.01  
% 2.61/1.01  
% 2.61/1.01  sim_fw_subset_subsumed:                 11
% 2.61/1.01  sim_bw_subset_subsumed:                 1
% 2.61/1.01  sim_fw_subsumed:                        4
% 2.61/1.01  sim_bw_subsumed:                        0
% 2.61/1.01  sim_fw_subsumption_res:                 1
% 2.61/1.01  sim_bw_subsumption_res:                 0
% 2.61/1.01  sim_tautology_del:                      1
% 2.61/1.01  sim_eq_tautology_del:                   1
% 2.61/1.01  sim_eq_res_simp:                        0
% 2.61/1.01  sim_fw_demodulated:                     0
% 2.61/1.01  sim_bw_demodulated:                     2
% 2.61/1.01  sim_light_normalised:                   5
% 2.61/1.01  sim_joinable_taut:                      0
% 2.61/1.01  sim_joinable_simp:                      0
% 2.61/1.01  sim_ac_normalised:                      0
% 2.61/1.01  sim_smt_subsumption:                    0
% 2.61/1.01  
%------------------------------------------------------------------------------
