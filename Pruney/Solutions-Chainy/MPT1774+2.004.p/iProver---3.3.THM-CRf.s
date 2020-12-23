%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:12 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  244 (1606 expanded)
%              Number of clauses        :  144 ( 281 expanded)
%              Number of leaves         :   25 ( 713 expanded)
%              Depth                    :   25
%              Number of atoms          : 1885 (34367 expanded)
%              Number of equality atoms :  372 (2325 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   50 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f113,plain,(
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
    inference(equality_resolution,[],[f84])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f61,plain,(
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
     => ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8)
          | ~ r1_tmap_1(X3,X0,X4,X6) )
        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8)
          | r1_tmap_1(X3,X0,X4,X6) )
        & sK8 = X6
        & r1_tarski(X5,u1_struct_0(X2))
        & r2_hidden(X6,X5)
        & v3_pre_topc(X5,X1)
        & m1_subset_1(sK8,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
              | ~ r1_tmap_1(X3,X0,X4,sK7) )
            & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
              | r1_tmap_1(X3,X0,X4,sK7) )
            & sK7 = X7
            & r1_tarski(X5,u1_struct_0(X2))
            & r2_hidden(sK7,X5)
            & v3_pre_topc(X5,X1)
            & m1_subset_1(X7,u1_struct_0(X2)) )
        & m1_subset_1(sK7,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
                & r1_tarski(sK6,u1_struct_0(X2))
                & r2_hidden(X6,sK6)
                & v3_pre_topc(sK6,X1)
                & m1_subset_1(X7,u1_struct_0(X2)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7)
                      | ~ r1_tmap_1(X3,X0,sK5,X6) )
                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7)
                      | r1_tmap_1(X3,X0,sK5,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(X2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,X1)
                    & m1_subset_1(X7,u1_struct_0(X2)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
                        ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7)
                          | ~ r1_tmap_1(sK4,X0,X4,X6) )
                        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7)
                          | r1_tmap_1(sK4,X0,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(X2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,X1)
                        & m1_subset_1(X7,u1_struct_0(X2)) )
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X2,sK4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X1)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
                            ( ( ~ r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7)
                              | ~ r1_tmap_1(X3,X0,X4,X6) )
                            & ( r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7)
                              | r1_tmap_1(X3,X0,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(sK3))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,X1)
                            & m1_subset_1(X7,u1_struct_0(sK3)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_pre_topc(sK3,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
                                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,X0,X4,X6) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,X0,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,sK2)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
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
                                  ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,sK1,X4,X6) )
                                  & ( r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,sK1,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
      | ~ r1_tmap_1(sK4,sK1,sK5,sK7) )
    & ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
      | r1_tmap_1(sK4,sK1,sK5,sK7) )
    & sK7 = sK8
    & r1_tarski(sK6,u1_struct_0(sK3))
    & r2_hidden(sK7,sK6)
    & v3_pre_topc(sK6,sK2)
    & m1_subset_1(sK8,u1_struct_0(sK3))
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_pre_topc(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f53,f61,f60,f59,f58,f57,f56,f55,f54])).

fof(f97,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f62])).

fof(f96,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f49,plain,(
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

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f114,plain,(
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
    inference(equality_resolution,[],[f83])).

fof(f13,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f112,plain,(
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
    inference(equality_resolution,[],[f82])).

fof(f95,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f99,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f86,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f87,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f88,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f98,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f62])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f91,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f94,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f90,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f89,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f108,plain,
    ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | ~ r1_tmap_1(sK4,sK1,sK5,sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f106,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f62])).

fof(f107,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | r1_tmap_1(sK4,sK1,sK5,sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f109,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f111,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f101,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f62])).

fof(f104,plain,(
    r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f62])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f110,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f105,plain,(
    r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f62])).

fof(f103,plain,(
    v3_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f102,plain,(
    m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f62])).

fof(f100,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f62])).

fof(f92,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f113])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_785,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_34])).

cnf(c_786,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_785])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_790,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_786,c_35])).

cnf(c_791,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_790])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_832,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_791,c_9])).

cnf(c_3983,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK4,X1,sK5,X0),X2)
    | r1_tmap_1(sK4,X1,sK5,X2)
    | ~ m1_connsp_2(X3,sK4,X2)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ r1_tarski(X3,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_5638,plain,
    ( r1_tmap_1(sK4,X0,sK5,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK4,X0,sK5,sK3),X1)
    | ~ m1_connsp_2(X2,sK4,X1)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK3))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3983])).

cnf(c_5781,plain,
    ( r1_tmap_1(sK4,X0,sK5,sK8)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK4,X0,sK5,sK3),sK8)
    | ~ m1_connsp_2(X1,sK4,sK8)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ r1_tarski(X1,u1_struct_0(sK3))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5638])).

cnf(c_11563,plain,
    ( r1_tmap_1(sK4,X0,sK5,sK8)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK4,X0,sK5,sK3),sK8)
    | ~ m1_connsp_2(u1_struct_0(sK3),sK4,sK8)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5781])).

cnf(c_11564,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(sK4,X0,sK5,sK8) = iProver_top
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK4,X0,sK5,sK3),sK8) != iProver_top
    | m1_connsp_2(u1_struct_0(sK3),sK4,sK8) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11563])).

cnf(c_11566,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK8) != iProver_top
    | m1_connsp_2(u1_struct_0(sK3),sK4,sK8) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11564])).

cnf(c_12,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4223,plain,
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
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_7311,plain,
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
    inference(instantiation,[status(thm)],[c_4223])).

cnf(c_10349,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK4,sK8)
    | ~ v3_pre_topc(sK6,sK4)
    | ~ r2_hidden(sK8,sK6)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK4))
    | ~ r1_tarski(sK6,u1_struct_0(sK3))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_7311])).

cnf(c_10350,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK4,sK8) = iProver_top
    | v3_pre_topc(sK6,sK4) != iProver_top
    | r2_hidden(sK8,sK6) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10349])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f114])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f112])).

cnf(c_237,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_19])).

cnf(c_238,plain,
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
    inference(renaming,[status(thm)],[c_237])).

cnf(c_728,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_238,c_34])).

cnf(c_729,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_728])).

cnf(c_733,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_729,c_35])).

cnf(c_734,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_733])).

cnf(c_769,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_734,c_9])).

cnf(c_3984,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(sK4,X1,sK5,X0),X2)
    | ~ r1_tmap_1(sK4,X1,sK5,X2)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_769])).

cnf(c_5633,plain,
    ( ~ r1_tmap_1(sK4,X0,sK5,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK4,X0,sK5,sK3),X1)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3984])).

cnf(c_9583,plain,
    ( ~ r1_tmap_1(sK4,X0,sK5,sK8)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK4,X0,sK5,sK3),sK8)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5633])).

cnf(c_9584,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(sK4,X0,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK4,X0,sK5,sK3),sK8) = iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9583])).

cnf(c_9586,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK8) = iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9584])).

cnf(c_36,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3014,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3016,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X4)) = k3_tmap_1(X3,X2,X1,X4,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_900,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X4))))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X4),X3,u1_struct_0(X2)) = k3_tmap_1(X1,X4,X0,X2,X3)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X4) != u1_struct_0(sK1)
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_34])).

cnf(c_901,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK5,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_900])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_905,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK5,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_901,c_35,c_22])).

cnf(c_906,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK5,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_905])).

cnf(c_2998,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_906])).

cnf(c_4099,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k3_tmap_1(X2,X0,sK4,X1,sK5)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2998])).

cnf(c_6558,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK4,X0,sK5)
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4099])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_46,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_47,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_48,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_58,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8183,plain,
    ( v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK4,X0,sK5)
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6558,c_46,c_47,c_48,c_58])).

cnf(c_8184,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK4,X0,sK5)
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_8183])).

cnf(c_8195,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK4,sK3,sK5)
    | m1_pre_topc(sK4,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3016,c_8184])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f80])).

cnf(c_948,plain,
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
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_34])).

cnf(c_949,plain,
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
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_948])).

cnf(c_953,plain,
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
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_949,c_35])).

cnf(c_954,plain,
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
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_953])).

cnf(c_2997,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK5,X2)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_954])).

cnf(c_3597,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2997])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_51,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_54,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3031,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4196,plain,
    ( l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3014,c_3031])).

cnf(c_4449,plain,
    ( l1_pre_topc(X0) != iProver_top
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3597,c_51,c_54,c_4196])).

cnf(c_4450,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4449])).

cnf(c_4463,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK1,sK5,X0)
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4450])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_50,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3032,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4648,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3014,c_3032])).

cnf(c_7449,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK1,sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4463,c_46,c_47,c_48,c_50,c_51,c_58,c_4648])).

cnf(c_7450,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK1,sK5,X0)
    | m1_pre_topc(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_7449])).

cnf(c_7457,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK1,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_3016,c_7450])).

cnf(c_8196,plain,
    ( k3_tmap_1(X0,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3)
    | m1_pre_topc(sK4,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8195,c_7457])).

cnf(c_8206,plain,
    ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3)
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3014,c_8196])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_49,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_8445,plain,
    ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8206,c_49,c_50,c_51])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_3024,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_25,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3111,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3024,c_25])).

cnf(c_8449,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8445,c_3111])).

cnf(c_24,negated_conjecture,
    ( r1_tmap_1(sK4,sK1,sK5,sK7)
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_3023,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3100,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3023,c_25])).

cnf(c_8448,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK8) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8445,c_3100])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3484,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6984,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_3484])).

cnf(c_6985,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6984])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_5677,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5680,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5677])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4837,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5676,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4837])).

cnf(c_5678,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5676])).

cnf(c_4842,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_3484])).

cnf(c_4843,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4842])).

cnf(c_3662,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(X0))
    | ~ r1_tarski(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4017,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3662])).

cnf(c_4018,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4017])).

cnf(c_10,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_3603,plain,
    ( v3_pre_topc(sK6,X0)
    | ~ v3_pre_topc(sK6,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3869,plain,
    ( v3_pre_topc(sK6,sK4)
    | ~ v3_pre_topc(sK6,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3603])).

cnf(c_3870,plain,
    ( v3_pre_topc(sK6,sK4) = iProver_top
    | v3_pre_topc(sK6,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3869])).

cnf(c_1993,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3454,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1993])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3018,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3069,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3018,c_25])).

cnf(c_27,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3021,plain,
    ( r2_hidden(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3064,plain,
    ( r2_hidden(sK8,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3021,c_25])).

cnf(c_2002,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_2017,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2002])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_121,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_117,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_65,plain,
    ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,negated_conjecture,
    ( v3_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_63,plain,
    ( v3_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_62,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_60,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_59,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_55,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_52,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11566,c_10350,c_9586,c_8449,c_8448,c_6985,c_5680,c_5678,c_4843,c_4648,c_4196,c_4018,c_3870,c_3454,c_3069,c_3064,c_2017,c_121,c_117,c_65,c_63,c_62,c_60,c_59,c_58,c_55,c_54,c_52,c_51,c_50,c_48,c_47,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:26:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.81/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/0.96  
% 3.81/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.81/0.96  
% 3.81/0.96  ------  iProver source info
% 3.81/0.96  
% 3.81/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.81/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.81/0.96  git: non_committed_changes: false
% 3.81/0.96  git: last_make_outside_of_git: false
% 3.81/0.96  
% 3.81/0.96  ------ 
% 3.81/0.96  
% 3.81/0.96  ------ Input Options
% 3.81/0.96  
% 3.81/0.96  --out_options                           all
% 3.81/0.96  --tptp_safe_out                         true
% 3.81/0.96  --problem_path                          ""
% 3.81/0.96  --include_path                          ""
% 3.81/0.96  --clausifier                            res/vclausify_rel
% 3.81/0.96  --clausifier_options                    --mode clausify
% 3.81/0.96  --stdin                                 false
% 3.81/0.96  --stats_out                             all
% 3.81/0.96  
% 3.81/0.96  ------ General Options
% 3.81/0.96  
% 3.81/0.96  --fof                                   false
% 3.81/0.96  --time_out_real                         305.
% 3.81/0.96  --time_out_virtual                      -1.
% 3.81/0.96  --symbol_type_check                     false
% 3.81/0.96  --clausify_out                          false
% 3.81/0.96  --sig_cnt_out                           false
% 3.81/0.96  --trig_cnt_out                          false
% 3.81/0.96  --trig_cnt_out_tolerance                1.
% 3.81/0.96  --trig_cnt_out_sk_spl                   false
% 3.81/0.96  --abstr_cl_out                          false
% 3.81/0.96  
% 3.81/0.96  ------ Global Options
% 3.81/0.96  
% 3.81/0.96  --schedule                              default
% 3.81/0.96  --add_important_lit                     false
% 3.81/0.96  --prop_solver_per_cl                    1000
% 3.81/0.96  --min_unsat_core                        false
% 3.81/0.96  --soft_assumptions                      false
% 3.81/0.96  --soft_lemma_size                       3
% 3.81/0.96  --prop_impl_unit_size                   0
% 3.81/0.96  --prop_impl_unit                        []
% 3.81/0.96  --share_sel_clauses                     true
% 3.81/0.96  --reset_solvers                         false
% 3.81/0.96  --bc_imp_inh                            [conj_cone]
% 3.81/0.96  --conj_cone_tolerance                   3.
% 3.81/0.96  --extra_neg_conj                        none
% 3.81/0.96  --large_theory_mode                     true
% 3.81/0.96  --prolific_symb_bound                   200
% 3.81/0.96  --lt_threshold                          2000
% 3.81/0.96  --clause_weak_htbl                      true
% 3.81/0.96  --gc_record_bc_elim                     false
% 3.81/0.96  
% 3.81/0.96  ------ Preprocessing Options
% 3.81/0.96  
% 3.81/0.96  --preprocessing_flag                    true
% 3.81/0.96  --time_out_prep_mult                    0.1
% 3.81/0.96  --splitting_mode                        input
% 3.81/0.96  --splitting_grd                         true
% 3.81/0.96  --splitting_cvd                         false
% 3.81/0.96  --splitting_cvd_svl                     false
% 3.81/0.96  --splitting_nvd                         32
% 3.81/0.96  --sub_typing                            true
% 3.81/0.96  --prep_gs_sim                           true
% 3.81/0.96  --prep_unflatten                        true
% 3.81/0.96  --prep_res_sim                          true
% 3.81/0.96  --prep_upred                            true
% 3.81/0.96  --prep_sem_filter                       exhaustive
% 3.81/0.96  --prep_sem_filter_out                   false
% 3.81/0.96  --pred_elim                             true
% 3.81/0.96  --res_sim_input                         true
% 3.81/0.96  --eq_ax_congr_red                       true
% 3.81/0.96  --pure_diseq_elim                       true
% 3.81/0.96  --brand_transform                       false
% 3.81/0.96  --non_eq_to_eq                          false
% 3.81/0.96  --prep_def_merge                        true
% 3.81/0.96  --prep_def_merge_prop_impl              false
% 3.81/0.96  --prep_def_merge_mbd                    true
% 3.81/0.96  --prep_def_merge_tr_red                 false
% 3.81/0.96  --prep_def_merge_tr_cl                  false
% 3.81/0.96  --smt_preprocessing                     true
% 3.81/0.96  --smt_ac_axioms                         fast
% 3.81/0.96  --preprocessed_out                      false
% 3.81/0.96  --preprocessed_stats                    false
% 3.81/0.96  
% 3.81/0.96  ------ Abstraction refinement Options
% 3.81/0.96  
% 3.81/0.96  --abstr_ref                             []
% 3.81/0.96  --abstr_ref_prep                        false
% 3.81/0.96  --abstr_ref_until_sat                   false
% 3.81/0.96  --abstr_ref_sig_restrict                funpre
% 3.81/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/0.96  --abstr_ref_under                       []
% 3.81/0.96  
% 3.81/0.96  ------ SAT Options
% 3.81/0.96  
% 3.81/0.96  --sat_mode                              false
% 3.81/0.96  --sat_fm_restart_options                ""
% 3.81/0.96  --sat_gr_def                            false
% 3.81/0.96  --sat_epr_types                         true
% 3.81/0.96  --sat_non_cyclic_types                  false
% 3.81/0.96  --sat_finite_models                     false
% 3.81/0.96  --sat_fm_lemmas                         false
% 3.81/0.96  --sat_fm_prep                           false
% 3.81/0.96  --sat_fm_uc_incr                        true
% 3.81/0.96  --sat_out_model                         small
% 3.81/0.96  --sat_out_clauses                       false
% 3.81/0.96  
% 3.81/0.96  ------ QBF Options
% 3.81/0.96  
% 3.81/0.96  --qbf_mode                              false
% 3.81/0.96  --qbf_elim_univ                         false
% 3.81/0.96  --qbf_dom_inst                          none
% 3.81/0.96  --qbf_dom_pre_inst                      false
% 3.81/0.96  --qbf_sk_in                             false
% 3.81/0.96  --qbf_pred_elim                         true
% 3.81/0.96  --qbf_split                             512
% 3.81/0.96  
% 3.81/0.96  ------ BMC1 Options
% 3.81/0.96  
% 3.81/0.96  --bmc1_incremental                      false
% 3.81/0.96  --bmc1_axioms                           reachable_all
% 3.81/0.96  --bmc1_min_bound                        0
% 3.81/0.96  --bmc1_max_bound                        -1
% 3.81/0.96  --bmc1_max_bound_default                -1
% 3.81/0.96  --bmc1_symbol_reachability              true
% 3.81/0.96  --bmc1_property_lemmas                  false
% 3.81/0.96  --bmc1_k_induction                      false
% 3.81/0.96  --bmc1_non_equiv_states                 false
% 3.81/0.96  --bmc1_deadlock                         false
% 3.81/0.96  --bmc1_ucm                              false
% 3.81/0.96  --bmc1_add_unsat_core                   none
% 3.81/0.96  --bmc1_unsat_core_children              false
% 3.81/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/0.96  --bmc1_out_stat                         full
% 3.81/0.96  --bmc1_ground_init                      false
% 3.81/0.96  --bmc1_pre_inst_next_state              false
% 3.81/0.96  --bmc1_pre_inst_state                   false
% 3.81/0.96  --bmc1_pre_inst_reach_state             false
% 3.81/0.96  --bmc1_out_unsat_core                   false
% 3.81/0.96  --bmc1_aig_witness_out                  false
% 3.81/0.96  --bmc1_verbose                          false
% 3.81/0.96  --bmc1_dump_clauses_tptp                false
% 3.81/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.81/0.96  --bmc1_dump_file                        -
% 3.81/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.81/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.81/0.96  --bmc1_ucm_extend_mode                  1
% 3.81/0.96  --bmc1_ucm_init_mode                    2
% 3.81/0.96  --bmc1_ucm_cone_mode                    none
% 3.81/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.81/0.96  --bmc1_ucm_relax_model                  4
% 3.81/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.81/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/0.96  --bmc1_ucm_layered_model                none
% 3.81/0.96  --bmc1_ucm_max_lemma_size               10
% 3.81/0.96  
% 3.81/0.96  ------ AIG Options
% 3.81/0.96  
% 3.81/0.96  --aig_mode                              false
% 3.81/0.96  
% 3.81/0.96  ------ Instantiation Options
% 3.81/0.96  
% 3.81/0.96  --instantiation_flag                    true
% 3.81/0.96  --inst_sos_flag                         false
% 3.81/0.96  --inst_sos_phase                        true
% 3.81/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/0.96  --inst_lit_sel_side                     num_symb
% 3.81/0.96  --inst_solver_per_active                1400
% 3.81/0.96  --inst_solver_calls_frac                1.
% 3.81/0.96  --inst_passive_queue_type               priority_queues
% 3.81/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/0.96  --inst_passive_queues_freq              [25;2]
% 3.81/0.96  --inst_dismatching                      true
% 3.81/0.96  --inst_eager_unprocessed_to_passive     true
% 3.81/0.96  --inst_prop_sim_given                   true
% 3.81/0.96  --inst_prop_sim_new                     false
% 3.81/0.96  --inst_subs_new                         false
% 3.81/0.96  --inst_eq_res_simp                      false
% 3.81/0.96  --inst_subs_given                       false
% 3.81/0.96  --inst_orphan_elimination               true
% 3.81/0.96  --inst_learning_loop_flag               true
% 3.81/0.96  --inst_learning_start                   3000
% 3.81/0.96  --inst_learning_factor                  2
% 3.81/0.96  --inst_start_prop_sim_after_learn       3
% 3.81/0.96  --inst_sel_renew                        solver
% 3.81/0.96  --inst_lit_activity_flag                true
% 3.81/0.96  --inst_restr_to_given                   false
% 3.81/0.96  --inst_activity_threshold               500
% 3.81/0.96  --inst_out_proof                        true
% 3.81/0.96  
% 3.81/0.96  ------ Resolution Options
% 3.81/0.96  
% 3.81/0.96  --resolution_flag                       true
% 3.81/0.96  --res_lit_sel                           adaptive
% 3.81/0.96  --res_lit_sel_side                      none
% 3.81/0.96  --res_ordering                          kbo
% 3.81/0.96  --res_to_prop_solver                    active
% 3.81/0.96  --res_prop_simpl_new                    false
% 3.81/0.96  --res_prop_simpl_given                  true
% 3.81/0.96  --res_passive_queue_type                priority_queues
% 3.81/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/0.96  --res_passive_queues_freq               [15;5]
% 3.81/0.96  --res_forward_subs                      full
% 3.81/0.96  --res_backward_subs                     full
% 3.81/0.96  --res_forward_subs_resolution           true
% 3.81/0.96  --res_backward_subs_resolution          true
% 3.81/0.96  --res_orphan_elimination                true
% 3.81/0.96  --res_time_limit                        2.
% 3.81/0.96  --res_out_proof                         true
% 3.81/0.96  
% 3.81/0.96  ------ Superposition Options
% 3.81/0.96  
% 3.81/0.96  --superposition_flag                    true
% 3.81/0.96  --sup_passive_queue_type                priority_queues
% 3.81/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.81/0.96  --demod_completeness_check              fast
% 3.81/0.96  --demod_use_ground                      true
% 3.81/0.96  --sup_to_prop_solver                    passive
% 3.81/0.96  --sup_prop_simpl_new                    true
% 3.81/0.96  --sup_prop_simpl_given                  true
% 3.81/0.96  --sup_fun_splitting                     false
% 3.81/0.96  --sup_smt_interval                      50000
% 3.81/0.96  
% 3.81/0.96  ------ Superposition Simplification Setup
% 3.81/0.96  
% 3.81/0.96  --sup_indices_passive                   []
% 3.81/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.96  --sup_full_bw                           [BwDemod]
% 3.81/0.96  --sup_immed_triv                        [TrivRules]
% 3.81/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.96  --sup_immed_bw_main                     []
% 3.81/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/0.96  
% 3.81/0.96  ------ Combination Options
% 3.81/0.96  
% 3.81/0.96  --comb_res_mult                         3
% 3.81/0.96  --comb_sup_mult                         2
% 3.81/0.96  --comb_inst_mult                        10
% 3.81/0.96  
% 3.81/0.96  ------ Debug Options
% 3.81/0.96  
% 3.81/0.96  --dbg_backtrace                         false
% 3.81/0.96  --dbg_dump_prop_clauses                 false
% 3.81/0.96  --dbg_dump_prop_clauses_file            -
% 3.81/0.96  --dbg_out_stat                          false
% 3.81/0.96  ------ Parsing...
% 3.81/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.81/0.96  
% 3.81/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.81/0.96  
% 3.81/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.81/0.96  
% 3.81/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/0.96  ------ Proving...
% 3.81/0.96  ------ Problem Properties 
% 3.81/0.96  
% 3.81/0.96  
% 3.81/0.96  clauses                                 42
% 3.81/0.96  conjectures                             21
% 3.81/0.96  EPR                                     19
% 3.81/0.96  Horn                                    30
% 3.81/0.96  unary                                   20
% 3.81/0.96  binary                                  4
% 3.81/0.96  lits                                    156
% 3.81/0.96  lits eq                                 12
% 3.81/0.96  fd_pure                                 0
% 3.81/0.96  fd_pseudo                               0
% 3.81/0.96  fd_cond                                 0
% 3.81/0.96  fd_pseudo_cond                          1
% 3.81/0.96  AC symbols                              0
% 3.81/0.96  
% 3.81/0.96  ------ Schedule dynamic 5 is on 
% 3.81/0.96  
% 3.81/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.81/0.96  
% 3.81/0.96  
% 3.81/0.96  ------ 
% 3.81/0.96  Current options:
% 3.81/0.96  ------ 
% 3.81/0.96  
% 3.81/0.96  ------ Input Options
% 3.81/0.96  
% 3.81/0.96  --out_options                           all
% 3.81/0.96  --tptp_safe_out                         true
% 3.81/0.96  --problem_path                          ""
% 3.81/0.96  --include_path                          ""
% 3.81/0.96  --clausifier                            res/vclausify_rel
% 3.81/0.96  --clausifier_options                    --mode clausify
% 3.81/0.96  --stdin                                 false
% 3.81/0.96  --stats_out                             all
% 3.81/0.96  
% 3.81/0.96  ------ General Options
% 3.81/0.96  
% 3.81/0.96  --fof                                   false
% 3.81/0.96  --time_out_real                         305.
% 3.81/0.96  --time_out_virtual                      -1.
% 3.81/0.96  --symbol_type_check                     false
% 3.81/0.96  --clausify_out                          false
% 3.81/0.96  --sig_cnt_out                           false
% 3.81/0.96  --trig_cnt_out                          false
% 3.81/0.96  --trig_cnt_out_tolerance                1.
% 3.81/0.96  --trig_cnt_out_sk_spl                   false
% 3.81/0.96  --abstr_cl_out                          false
% 3.81/0.96  
% 3.81/0.96  ------ Global Options
% 3.81/0.96  
% 3.81/0.96  --schedule                              default
% 3.81/0.96  --add_important_lit                     false
% 3.81/0.96  --prop_solver_per_cl                    1000
% 3.81/0.96  --min_unsat_core                        false
% 3.81/0.96  --soft_assumptions                      false
% 3.81/0.96  --soft_lemma_size                       3
% 3.81/0.96  --prop_impl_unit_size                   0
% 3.81/0.96  --prop_impl_unit                        []
% 3.81/0.96  --share_sel_clauses                     true
% 3.81/0.96  --reset_solvers                         false
% 3.81/0.96  --bc_imp_inh                            [conj_cone]
% 3.81/0.96  --conj_cone_tolerance                   3.
% 3.81/0.96  --extra_neg_conj                        none
% 3.81/0.96  --large_theory_mode                     true
% 3.81/0.96  --prolific_symb_bound                   200
% 3.81/0.96  --lt_threshold                          2000
% 3.81/0.96  --clause_weak_htbl                      true
% 3.81/0.96  --gc_record_bc_elim                     false
% 3.81/0.96  
% 3.81/0.96  ------ Preprocessing Options
% 3.81/0.96  
% 3.81/0.96  --preprocessing_flag                    true
% 3.81/0.96  --time_out_prep_mult                    0.1
% 3.81/0.96  --splitting_mode                        input
% 3.81/0.96  --splitting_grd                         true
% 3.81/0.96  --splitting_cvd                         false
% 3.81/0.96  --splitting_cvd_svl                     false
% 3.81/0.96  --splitting_nvd                         32
% 3.81/0.96  --sub_typing                            true
% 3.81/0.96  --prep_gs_sim                           true
% 3.81/0.96  --prep_unflatten                        true
% 3.81/0.96  --prep_res_sim                          true
% 3.81/0.96  --prep_upred                            true
% 3.81/0.96  --prep_sem_filter                       exhaustive
% 3.81/0.96  --prep_sem_filter_out                   false
% 3.81/0.96  --pred_elim                             true
% 3.81/0.96  --res_sim_input                         true
% 3.81/0.96  --eq_ax_congr_red                       true
% 3.81/0.96  --pure_diseq_elim                       true
% 3.81/0.96  --brand_transform                       false
% 3.81/0.96  --non_eq_to_eq                          false
% 3.81/0.96  --prep_def_merge                        true
% 3.81/0.96  --prep_def_merge_prop_impl              false
% 3.81/0.96  --prep_def_merge_mbd                    true
% 3.81/0.96  --prep_def_merge_tr_red                 false
% 3.81/0.96  --prep_def_merge_tr_cl                  false
% 3.81/0.96  --smt_preprocessing                     true
% 3.81/0.96  --smt_ac_axioms                         fast
% 3.81/0.96  --preprocessed_out                      false
% 3.81/0.96  --preprocessed_stats                    false
% 3.81/0.96  
% 3.81/0.96  ------ Abstraction refinement Options
% 3.81/0.96  
% 3.81/0.96  --abstr_ref                             []
% 3.81/0.96  --abstr_ref_prep                        false
% 3.81/0.96  --abstr_ref_until_sat                   false
% 3.81/0.96  --abstr_ref_sig_restrict                funpre
% 3.81/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/0.96  --abstr_ref_under                       []
% 3.81/0.96  
% 3.81/0.96  ------ SAT Options
% 3.81/0.96  
% 3.81/0.96  --sat_mode                              false
% 3.81/0.96  --sat_fm_restart_options                ""
% 3.81/0.96  --sat_gr_def                            false
% 3.81/0.96  --sat_epr_types                         true
% 3.81/0.96  --sat_non_cyclic_types                  false
% 3.81/0.96  --sat_finite_models                     false
% 3.81/0.96  --sat_fm_lemmas                         false
% 3.81/0.96  --sat_fm_prep                           false
% 3.81/0.96  --sat_fm_uc_incr                        true
% 3.81/0.96  --sat_out_model                         small
% 3.81/0.96  --sat_out_clauses                       false
% 3.81/0.96  
% 3.81/0.96  ------ QBF Options
% 3.81/0.96  
% 3.81/0.96  --qbf_mode                              false
% 3.81/0.96  --qbf_elim_univ                         false
% 3.81/0.96  --qbf_dom_inst                          none
% 3.81/0.96  --qbf_dom_pre_inst                      false
% 3.81/0.96  --qbf_sk_in                             false
% 3.81/0.96  --qbf_pred_elim                         true
% 3.81/0.96  --qbf_split                             512
% 3.81/0.96  
% 3.81/0.96  ------ BMC1 Options
% 3.81/0.96  
% 3.81/0.96  --bmc1_incremental                      false
% 3.81/0.96  --bmc1_axioms                           reachable_all
% 3.81/0.96  --bmc1_min_bound                        0
% 3.81/0.96  --bmc1_max_bound                        -1
% 3.81/0.96  --bmc1_max_bound_default                -1
% 3.81/0.96  --bmc1_symbol_reachability              true
% 3.81/0.96  --bmc1_property_lemmas                  false
% 3.81/0.96  --bmc1_k_induction                      false
% 3.81/0.96  --bmc1_non_equiv_states                 false
% 3.81/0.96  --bmc1_deadlock                         false
% 3.81/0.96  --bmc1_ucm                              false
% 3.81/0.96  --bmc1_add_unsat_core                   none
% 3.81/0.96  --bmc1_unsat_core_children              false
% 3.81/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/0.96  --bmc1_out_stat                         full
% 3.81/0.96  --bmc1_ground_init                      false
% 3.81/0.96  --bmc1_pre_inst_next_state              false
% 3.81/0.96  --bmc1_pre_inst_state                   false
% 3.81/0.96  --bmc1_pre_inst_reach_state             false
% 3.81/0.96  --bmc1_out_unsat_core                   false
% 3.81/0.96  --bmc1_aig_witness_out                  false
% 3.81/0.96  --bmc1_verbose                          false
% 3.81/0.96  --bmc1_dump_clauses_tptp                false
% 3.81/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.81/0.96  --bmc1_dump_file                        -
% 3.81/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.81/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.81/0.96  --bmc1_ucm_extend_mode                  1
% 3.81/0.96  --bmc1_ucm_init_mode                    2
% 3.81/0.96  --bmc1_ucm_cone_mode                    none
% 3.81/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.81/0.96  --bmc1_ucm_relax_model                  4
% 3.81/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.81/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/0.96  --bmc1_ucm_layered_model                none
% 3.81/0.96  --bmc1_ucm_max_lemma_size               10
% 3.81/0.96  
% 3.81/0.96  ------ AIG Options
% 3.81/0.96  
% 3.81/0.96  --aig_mode                              false
% 3.81/0.96  
% 3.81/0.96  ------ Instantiation Options
% 3.81/0.96  
% 3.81/0.96  --instantiation_flag                    true
% 3.81/0.96  --inst_sos_flag                         false
% 3.81/0.96  --inst_sos_phase                        true
% 3.81/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/0.96  --inst_lit_sel_side                     none
% 3.81/0.96  --inst_solver_per_active                1400
% 3.81/0.96  --inst_solver_calls_frac                1.
% 3.81/0.96  --inst_passive_queue_type               priority_queues
% 3.81/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/0.96  --inst_passive_queues_freq              [25;2]
% 3.81/0.96  --inst_dismatching                      true
% 3.81/0.96  --inst_eager_unprocessed_to_passive     true
% 3.81/0.96  --inst_prop_sim_given                   true
% 3.81/0.96  --inst_prop_sim_new                     false
% 3.81/0.96  --inst_subs_new                         false
% 3.81/0.96  --inst_eq_res_simp                      false
% 3.81/0.96  --inst_subs_given                       false
% 3.81/0.96  --inst_orphan_elimination               true
% 3.81/0.96  --inst_learning_loop_flag               true
% 3.81/0.96  --inst_learning_start                   3000
% 3.81/0.96  --inst_learning_factor                  2
% 3.81/0.96  --inst_start_prop_sim_after_learn       3
% 3.81/0.96  --inst_sel_renew                        solver
% 3.81/0.96  --inst_lit_activity_flag                true
% 3.81/0.96  --inst_restr_to_given                   false
% 3.81/0.96  --inst_activity_threshold               500
% 3.81/0.96  --inst_out_proof                        true
% 3.81/0.96  
% 3.81/0.96  ------ Resolution Options
% 3.81/0.96  
% 3.81/0.96  --resolution_flag                       false
% 3.81/0.96  --res_lit_sel                           adaptive
% 3.81/0.96  --res_lit_sel_side                      none
% 3.81/0.96  --res_ordering                          kbo
% 3.81/0.96  --res_to_prop_solver                    active
% 3.81/0.96  --res_prop_simpl_new                    false
% 3.81/0.96  --res_prop_simpl_given                  true
% 3.81/0.96  --res_passive_queue_type                priority_queues
% 3.81/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/0.96  --res_passive_queues_freq               [15;5]
% 3.81/0.96  --res_forward_subs                      full
% 3.81/0.96  --res_backward_subs                     full
% 3.81/0.96  --res_forward_subs_resolution           true
% 3.81/0.96  --res_backward_subs_resolution          true
% 3.81/0.96  --res_orphan_elimination                true
% 3.81/0.96  --res_time_limit                        2.
% 3.81/0.96  --res_out_proof                         true
% 3.81/0.96  
% 3.81/0.96  ------ Superposition Options
% 3.81/0.96  
% 3.81/0.96  --superposition_flag                    true
% 3.81/0.96  --sup_passive_queue_type                priority_queues
% 3.81/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.81/0.96  --demod_completeness_check              fast
% 3.81/0.96  --demod_use_ground                      true
% 3.81/0.96  --sup_to_prop_solver                    passive
% 3.81/0.96  --sup_prop_simpl_new                    true
% 3.81/0.96  --sup_prop_simpl_given                  true
% 3.81/0.96  --sup_fun_splitting                     false
% 3.81/0.96  --sup_smt_interval                      50000
% 3.81/0.96  
% 3.81/0.96  ------ Superposition Simplification Setup
% 3.81/0.96  
% 3.81/0.96  --sup_indices_passive                   []
% 3.81/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.96  --sup_full_bw                           [BwDemod]
% 3.81/0.96  --sup_immed_triv                        [TrivRules]
% 3.81/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.96  --sup_immed_bw_main                     []
% 3.81/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/0.96  
% 3.81/0.96  ------ Combination Options
% 3.81/0.96  
% 3.81/0.96  --comb_res_mult                         3
% 3.81/0.96  --comb_sup_mult                         2
% 3.81/0.96  --comb_inst_mult                        10
% 3.81/0.96  
% 3.81/0.96  ------ Debug Options
% 3.81/0.96  
% 3.81/0.96  --dbg_backtrace                         false
% 3.81/0.96  --dbg_dump_prop_clauses                 false
% 3.81/0.96  --dbg_dump_prop_clauses_file            -
% 3.81/0.96  --dbg_out_stat                          false
% 3.81/0.96  
% 3.81/0.96  
% 3.81/0.96  
% 3.81/0.96  
% 3.81/0.96  ------ Proving...
% 3.81/0.96  
% 3.81/0.96  
% 3.81/0.96  % SZS status Theorem for theBenchmark.p
% 3.81/0.96  
% 3.81/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.81/0.96  
% 3.81/0.96  fof(f14,axiom,(
% 3.81/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 3.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.96  
% 3.81/0.96  fof(f38,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.81/0.96    inference(ennf_transformation,[],[f14])).
% 3.81/0.96  
% 3.81/0.96  fof(f39,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.96    inference(flattening,[],[f38])).
% 3.81/0.96  
% 3.81/0.96  fof(f51,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.96    inference(nnf_transformation,[],[f39])).
% 3.81/0.96  
% 3.81/0.96  fof(f84,plain,(
% 3.81/0.96    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.96    inference(cnf_transformation,[],[f51])).
% 3.81/0.96  
% 3.81/0.96  fof(f113,plain,(
% 3.81/0.96    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.96    inference(equality_resolution,[],[f84])).
% 3.81/0.96  
% 3.81/0.96  fof(f16,conjecture,(
% 3.81/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 3.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.96  
% 3.81/0.96  fof(f17,negated_conjecture,(
% 3.81/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 3.81/0.96    inference(negated_conjecture,[],[f16])).
% 3.81/0.96  
% 3.81/0.96  fof(f42,plain,(
% 3.81/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.81/0.96    inference(ennf_transformation,[],[f17])).
% 3.81/0.96  
% 3.81/0.96  fof(f43,plain,(
% 3.81/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.81/0.96    inference(flattening,[],[f42])).
% 3.81/0.96  
% 3.81/0.96  fof(f52,plain,(
% 3.81/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.81/0.96    inference(nnf_transformation,[],[f43])).
% 3.81/0.96  
% 3.81/0.96  fof(f53,plain,(
% 3.81/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.81/0.96    inference(flattening,[],[f52])).
% 3.81/0.96  
% 3.81/0.96  fof(f61,plain,(
% 3.81/0.96    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8) | r1_tmap_1(X3,X0,X4,X6)) & sK8 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(sK8,u1_struct_0(X2)))) )),
% 3.81/0.96    introduced(choice_axiom,[])).
% 3.81/0.96  
% 3.81/0.96  fof(f60,plain,(
% 3.81/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,sK7)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,sK7)) & sK7 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK7,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 3.81/0.96    introduced(choice_axiom,[])).
% 3.81/0.96  
% 3.81/0.96  fof(f59,plain,(
% 3.81/0.96    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(sK6,u1_struct_0(X2)) & r2_hidden(X6,sK6) & v3_pre_topc(sK6,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 3.81/0.96    introduced(choice_axiom,[])).
% 3.81/0.96  
% 3.81/0.96  fof(f58,plain,(
% 3.81/0.96    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7) | ~r1_tmap_1(X3,X0,sK5,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7) | r1_tmap_1(X3,X0,sK5,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 3.81/0.96    introduced(choice_axiom,[])).
% 3.81/0.96  
% 3.81/0.96  fof(f57,plain,(
% 3.81/0.96    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7) | ~r1_tmap_1(sK4,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7) | r1_tmap_1(sK4,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X1) & ~v2_struct_0(sK4))) )),
% 3.81/0.96    introduced(choice_axiom,[])).
% 3.81/0.96  
% 3.81/0.96  fof(f56,plain,(
% 3.81/0.96    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK3)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(sK3))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 3.81/0.96    introduced(choice_axiom,[])).
% 3.81/0.96  
% 3.81/0.96  fof(f55,plain,(
% 3.81/0.96    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK2) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 3.81/0.96    introduced(choice_axiom,[])).
% 3.81/0.96  
% 3.81/0.96  fof(f54,plain,(
% 3.81/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.81/0.96    introduced(choice_axiom,[])).
% 3.81/0.96  
% 3.81/0.96  fof(f62,plain,(
% 3.81/0.96    ((((((((~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK1,sK5,sK7)) & (r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK1,sK5,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK3)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK2) & m1_subset_1(sK8,u1_struct_0(sK3))) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.81/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f53,f61,f60,f59,f58,f57,f56,f55,f54])).
% 3.81/0.96  
% 3.81/0.96  fof(f97,plain,(
% 3.81/0.96    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1))),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f96,plain,(
% 3.81/0.96    v1_funct_1(sK5)),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f7,axiom,(
% 3.81/0.96    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.96  
% 3.81/0.96  fof(f24,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.81/0.96    inference(ennf_transformation,[],[f7])).
% 3.81/0.96  
% 3.81/0.96  fof(f25,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.96    inference(flattening,[],[f24])).
% 3.81/0.96  
% 3.81/0.96  fof(f72,plain,(
% 3.81/0.96    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.96    inference(cnf_transformation,[],[f25])).
% 3.81/0.96  
% 3.81/0.96  fof(f10,axiom,(
% 3.81/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 3.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.96  
% 3.81/0.96  fof(f30,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.81/0.96    inference(ennf_transformation,[],[f10])).
% 3.81/0.96  
% 3.81/0.96  fof(f31,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.96    inference(flattening,[],[f30])).
% 3.81/0.96  
% 3.81/0.96  fof(f47,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.96    inference(nnf_transformation,[],[f31])).
% 3.81/0.96  
% 3.81/0.96  fof(f48,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.96    inference(rectify,[],[f47])).
% 3.81/0.96  
% 3.81/0.96  fof(f49,plain,(
% 3.81/0.96    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK0(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.81/0.96    introduced(choice_axiom,[])).
% 3.81/0.96  
% 3.81/0.96  fof(f50,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK0(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 3.81/0.96  
% 3.81/0.96  fof(f79,plain,(
% 3.81/0.96    ( ! [X2,X0,X3,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.96    inference(cnf_transformation,[],[f50])).
% 3.81/0.96  
% 3.81/0.96  fof(f83,plain,(
% 3.81/0.96    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.96    inference(cnf_transformation,[],[f51])).
% 3.81/0.96  
% 3.81/0.96  fof(f114,plain,(
% 3.81/0.96    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.96    inference(equality_resolution,[],[f83])).
% 3.81/0.96  
% 3.81/0.96  fof(f13,axiom,(
% 3.81/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 3.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.96  
% 3.81/0.96  fof(f36,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.81/0.96    inference(ennf_transformation,[],[f13])).
% 3.81/0.96  
% 3.81/0.96  fof(f37,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.96    inference(flattening,[],[f36])).
% 3.81/0.96  
% 3.81/0.96  fof(f82,plain,(
% 3.81/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.96    inference(cnf_transformation,[],[f37])).
% 3.81/0.96  
% 3.81/0.96  fof(f112,plain,(
% 3.81/0.96    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.96    inference(equality_resolution,[],[f82])).
% 3.81/0.96  
% 3.81/0.96  fof(f95,plain,(
% 3.81/0.96    m1_pre_topc(sK4,sK2)),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f99,plain,(
% 3.81/0.96    m1_pre_topc(sK3,sK4)),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f12,axiom,(
% 3.81/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.96  
% 3.81/0.96  fof(f34,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.81/0.96    inference(ennf_transformation,[],[f12])).
% 3.81/0.96  
% 3.81/0.96  fof(f35,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.96    inference(flattening,[],[f34])).
% 3.81/0.96  
% 3.81/0.96  fof(f81,plain,(
% 3.81/0.96    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.96    inference(cnf_transformation,[],[f35])).
% 3.81/0.96  
% 3.81/0.96  fof(f15,axiom,(
% 3.81/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.96  
% 3.81/0.96  fof(f40,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.81/0.96    inference(ennf_transformation,[],[f15])).
% 3.81/0.96  
% 3.81/0.96  fof(f41,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.81/0.96    inference(flattening,[],[f40])).
% 3.81/0.96  
% 3.81/0.96  fof(f85,plain,(
% 3.81/0.96    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.81/0.96    inference(cnf_transformation,[],[f41])).
% 3.81/0.96  
% 3.81/0.96  fof(f86,plain,(
% 3.81/0.96    ~v2_struct_0(sK1)),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f87,plain,(
% 3.81/0.96    v2_pre_topc(sK1)),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f88,plain,(
% 3.81/0.96    l1_pre_topc(sK1)),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f98,plain,(
% 3.81/0.96    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f11,axiom,(
% 3.81/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.96  
% 3.81/0.96  fof(f32,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.81/0.96    inference(ennf_transformation,[],[f11])).
% 3.81/0.96  
% 3.81/0.96  fof(f33,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.96    inference(flattening,[],[f32])).
% 3.81/0.96  
% 3.81/0.96  fof(f80,plain,(
% 3.81/0.96    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.96    inference(cnf_transformation,[],[f33])).
% 3.81/0.96  
% 3.81/0.96  fof(f91,plain,(
% 3.81/0.96    l1_pre_topc(sK2)),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f94,plain,(
% 3.81/0.96    ~v2_struct_0(sK4)),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f5,axiom,(
% 3.81/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.96  
% 3.81/0.96  fof(f22,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.81/0.96    inference(ennf_transformation,[],[f5])).
% 3.81/0.96  
% 3.81/0.96  fof(f70,plain,(
% 3.81/0.96    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.81/0.96    inference(cnf_transformation,[],[f22])).
% 3.81/0.96  
% 3.81/0.96  fof(f90,plain,(
% 3.81/0.96    v2_pre_topc(sK2)),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f4,axiom,(
% 3.81/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.96  
% 3.81/0.96  fof(f20,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.81/0.96    inference(ennf_transformation,[],[f4])).
% 3.81/0.96  
% 3.81/0.96  fof(f21,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.81/0.96    inference(flattening,[],[f20])).
% 3.81/0.96  
% 3.81/0.96  fof(f69,plain,(
% 3.81/0.96    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.81/0.96    inference(cnf_transformation,[],[f21])).
% 3.81/0.96  
% 3.81/0.96  fof(f89,plain,(
% 3.81/0.96    ~v2_struct_0(sK2)),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f108,plain,(
% 3.81/0.96    ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK1,sK5,sK7)),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f106,plain,(
% 3.81/0.96    sK7 = sK8),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f107,plain,(
% 3.81/0.96    r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK1,sK5,sK7)),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f6,axiom,(
% 3.81/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.96  
% 3.81/0.96  fof(f23,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.81/0.96    inference(ennf_transformation,[],[f6])).
% 3.81/0.96  
% 3.81/0.96  fof(f71,plain,(
% 3.81/0.96    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.81/0.96    inference(cnf_transformation,[],[f23])).
% 3.81/0.96  
% 3.81/0.96  fof(f1,axiom,(
% 3.81/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.96  
% 3.81/0.96  fof(f44,plain,(
% 3.81/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.81/0.96    inference(nnf_transformation,[],[f1])).
% 3.81/0.96  
% 3.81/0.96  fof(f45,plain,(
% 3.81/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.81/0.96    inference(flattening,[],[f44])).
% 3.81/0.96  
% 3.81/0.96  fof(f64,plain,(
% 3.81/0.96    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.81/0.96    inference(cnf_transformation,[],[f45])).
% 3.81/0.96  
% 3.81/0.96  fof(f109,plain,(
% 3.81/0.96    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.81/0.96    inference(equality_resolution,[],[f64])).
% 3.81/0.96  
% 3.81/0.96  fof(f2,axiom,(
% 3.81/0.96    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.96  
% 3.81/0.96  fof(f46,plain,(
% 3.81/0.96    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.81/0.96    inference(nnf_transformation,[],[f2])).
% 3.81/0.96  
% 3.81/0.96  fof(f67,plain,(
% 3.81/0.96    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.81/0.96    inference(cnf_transformation,[],[f46])).
% 3.81/0.96  
% 3.81/0.96  fof(f8,axiom,(
% 3.81/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 3.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.96  
% 3.81/0.96  fof(f26,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.81/0.96    inference(ennf_transformation,[],[f8])).
% 3.81/0.96  
% 3.81/0.96  fof(f27,plain,(
% 3.81/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.81/0.96    inference(flattening,[],[f26])).
% 3.81/0.96  
% 3.81/0.96  fof(f73,plain,(
% 3.81/0.96    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.81/0.96    inference(cnf_transformation,[],[f27])).
% 3.81/0.96  
% 3.81/0.96  fof(f111,plain,(
% 3.81/0.96    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.81/0.96    inference(equality_resolution,[],[f73])).
% 3.81/0.96  
% 3.81/0.96  fof(f101,plain,(
% 3.81/0.96    m1_subset_1(sK7,u1_struct_0(sK4))),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f104,plain,(
% 3.81/0.96    r2_hidden(sK7,sK6)),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f65,plain,(
% 3.81/0.96    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.81/0.96    inference(cnf_transformation,[],[f45])).
% 3.81/0.96  
% 3.81/0.96  fof(f63,plain,(
% 3.81/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.81/0.96    inference(cnf_transformation,[],[f45])).
% 3.81/0.96  
% 3.81/0.96  fof(f110,plain,(
% 3.81/0.96    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.81/0.96    inference(equality_resolution,[],[f63])).
% 3.81/0.96  
% 3.81/0.96  fof(f105,plain,(
% 3.81/0.96    r1_tarski(sK6,u1_struct_0(sK3))),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f103,plain,(
% 3.81/0.96    v3_pre_topc(sK6,sK2)),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f102,plain,(
% 3.81/0.96    m1_subset_1(sK8,u1_struct_0(sK3))),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f100,plain,(
% 3.81/0.96    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  fof(f92,plain,(
% 3.81/0.96    ~v2_struct_0(sK3)),
% 3.81/0.96    inference(cnf_transformation,[],[f62])).
% 3.81/0.96  
% 3.81/0.96  cnf(c_20,plain,
% 3.81/0.96      ( r1_tmap_1(X0,X1,X2,X3)
% 3.81/0.96      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.81/0.96      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.81/0.96      | ~ m1_connsp_2(X5,X0,X3)
% 3.81/0.96      | ~ m1_pre_topc(X4,X0)
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.81/0.96      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.81/0.96      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.81/0.96      | ~ v1_funct_1(X2)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(X4)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(X0)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X0) ),
% 3.81/0.96      inference(cnf_transformation,[],[f113]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_34,negated_conjecture,
% 3.81/0.96      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
% 3.81/0.96      inference(cnf_transformation,[],[f97]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_785,plain,
% 3.81/0.96      ( r1_tmap_1(X0,X1,X2,X3)
% 3.81/0.96      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.81/0.96      | ~ m1_connsp_2(X5,X0,X3)
% 3.81/0.96      | ~ m1_pre_topc(X4,X0)
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.81/0.96      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.81/0.96      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.81/0.96      | ~ v1_funct_1(X2)
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X4)
% 3.81/0.96      | ~ l1_pre_topc(X0)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X0)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.81/0.96      | sK5 != X2 ),
% 3.81/0.96      inference(resolution_lifted,[status(thm)],[c_20,c_34]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_786,plain,
% 3.81/0.96      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.81/0.96      | r1_tmap_1(X2,X1,sK5,X3)
% 3.81/0.96      | ~ m1_connsp_2(X4,X2,X3)
% 3.81/0.96      | ~ m1_pre_topc(X0,X2)
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.81/0.96      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.81/0.96      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.81/0.96      | ~ v1_funct_1(sK5)
% 3.81/0.96      | v2_struct_0(X2)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | ~ l1_pre_topc(X2)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X2)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.81/0.96      inference(unflattening,[status(thm)],[c_785]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_35,negated_conjecture,
% 3.81/0.96      ( v1_funct_1(sK5) ),
% 3.81/0.96      inference(cnf_transformation,[],[f96]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_790,plain,
% 3.81/0.96      ( ~ r1_tarski(X4,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.81/0.96      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_pre_topc(X0,X2)
% 3.81/0.96      | ~ m1_connsp_2(X4,X2,X3)
% 3.81/0.96      | r1_tmap_1(X2,X1,sK5,X3)
% 3.81/0.96      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.81/0.96      | v2_struct_0(X2)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | ~ l1_pre_topc(X2)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X2)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.81/0.96      inference(global_propositional_subsumption,
% 3.81/0.96                [status(thm)],
% 3.81/0.96                [c_786,c_35]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_791,plain,
% 3.81/0.96      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.81/0.96      | r1_tmap_1(X2,X1,sK5,X3)
% 3.81/0.96      | ~ m1_connsp_2(X4,X2,X3)
% 3.81/0.96      | ~ m1_pre_topc(X0,X2)
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.81/0.96      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.81/0.96      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X2)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(X2)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X2)
% 3.81/0.96      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.81/0.96      inference(renaming,[status(thm)],[c_790]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_9,plain,
% 3.81/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.81/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.81/0.96      | m1_subset_1(X2,u1_struct_0(X1))
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | ~ l1_pre_topc(X1) ),
% 3.81/0.96      inference(cnf_transformation,[],[f72]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_832,plain,
% 3.81/0.96      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.81/0.96      | r1_tmap_1(X2,X1,sK5,X3)
% 3.81/0.96      | ~ m1_connsp_2(X4,X2,X3)
% 3.81/0.96      | ~ m1_pre_topc(X0,X2)
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.81/0.96      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X2)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(X2)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X2)
% 3.81/0.96      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.81/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_791,c_9]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3983,plain,
% 3.81/0.96      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK4,X1,sK5,X0),X2)
% 3.81/0.96      | r1_tmap_1(sK4,X1,sK5,X2)
% 3.81/0.96      | ~ m1_connsp_2(X3,sK4,X2)
% 3.81/0.96      | ~ m1_pre_topc(X0,sK4)
% 3.81/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 3.81/0.96      | ~ r1_tarski(X3,u1_struct_0(X0))
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(sK4)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(sK4)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(sK4)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.81/0.96      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_832]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_5638,plain,
% 3.81/0.96      ( r1_tmap_1(sK4,X0,sK5,X1)
% 3.81/0.96      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK4,X0,sK5,sK3),X1)
% 3.81/0.96      | ~ m1_connsp_2(X2,sK4,X1)
% 3.81/0.96      | ~ m1_pre_topc(sK3,sK4)
% 3.81/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.81/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 3.81/0.96      | ~ r1_tarski(X2,u1_struct_0(sK3))
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(sK4)
% 3.81/0.96      | v2_struct_0(sK3)
% 3.81/0.96      | ~ l1_pre_topc(X0)
% 3.81/0.96      | ~ l1_pre_topc(sK4)
% 3.81/0.96      | ~ v2_pre_topc(X0)
% 3.81/0.96      | ~ v2_pre_topc(sK4)
% 3.81/0.96      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.81/0.96      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_3983]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_5781,plain,
% 3.81/0.96      ( r1_tmap_1(sK4,X0,sK5,sK8)
% 3.81/0.96      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK4,X0,sK5,sK3),sK8)
% 3.81/0.96      | ~ m1_connsp_2(X1,sK4,sK8)
% 3.81/0.96      | ~ m1_pre_topc(sK3,sK4)
% 3.81/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.81/0.96      | ~ m1_subset_1(sK8,u1_struct_0(sK3))
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 3.81/0.96      | ~ r1_tarski(X1,u1_struct_0(sK3))
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(sK4)
% 3.81/0.96      | v2_struct_0(sK3)
% 3.81/0.96      | ~ l1_pre_topc(X0)
% 3.81/0.96      | ~ l1_pre_topc(sK4)
% 3.81/0.96      | ~ v2_pre_topc(X0)
% 3.81/0.96      | ~ v2_pre_topc(sK4)
% 3.81/0.96      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.81/0.96      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_5638]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_11563,plain,
% 3.81/0.96      ( r1_tmap_1(sK4,X0,sK5,sK8)
% 3.81/0.96      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK4,X0,sK5,sK3),sK8)
% 3.81/0.96      | ~ m1_connsp_2(u1_struct_0(sK3),sK4,sK8)
% 3.81/0.96      | ~ m1_pre_topc(sK3,sK4)
% 3.81/0.96      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.81/0.96      | ~ m1_subset_1(sK8,u1_struct_0(sK3))
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 3.81/0.96      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(sK4)
% 3.81/0.96      | v2_struct_0(sK3)
% 3.81/0.96      | ~ l1_pre_topc(X0)
% 3.81/0.96      | ~ l1_pre_topc(sK4)
% 3.81/0.96      | ~ v2_pre_topc(X0)
% 3.81/0.96      | ~ v2_pre_topc(sK4)
% 3.81/0.96      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.81/0.96      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_5781]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_11564,plain,
% 3.81/0.96      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.81/0.96      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 3.81/0.96      | r1_tmap_1(sK4,X0,sK5,sK8) = iProver_top
% 3.81/0.96      | r1_tmap_1(sK3,X0,k2_tmap_1(sK4,X0,sK5,sK3),sK8) != iProver_top
% 3.81/0.96      | m1_connsp_2(u1_struct_0(sK3),sK4,sK8) != iProver_top
% 3.81/0.96      | m1_pre_topc(sK3,sK4) != iProver_top
% 3.81/0.96      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.81/0.96      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 3.81/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.81/0.96      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 3.81/0.96      | v2_struct_0(X0) = iProver_top
% 3.81/0.96      | v2_struct_0(sK4) = iProver_top
% 3.81/0.96      | v2_struct_0(sK3) = iProver_top
% 3.81/0.96      | l1_pre_topc(X0) != iProver_top
% 3.81/0.96      | l1_pre_topc(sK4) != iProver_top
% 3.81/0.96      | v2_pre_topc(X0) != iProver_top
% 3.81/0.96      | v2_pre_topc(sK4) != iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_11563]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_11566,plain,
% 3.81/0.96      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.81/0.96      | r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
% 3.81/0.96      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK8) != iProver_top
% 3.81/0.96      | m1_connsp_2(u1_struct_0(sK3),sK4,sK8) != iProver_top
% 3.81/0.96      | m1_pre_topc(sK3,sK4) != iProver_top
% 3.81/0.96      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.81/0.96      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 3.81/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 3.81/0.96      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 3.81/0.96      | v2_struct_0(sK4) = iProver_top
% 3.81/0.96      | v2_struct_0(sK1) = iProver_top
% 3.81/0.96      | v2_struct_0(sK3) = iProver_top
% 3.81/0.96      | l1_pre_topc(sK4) != iProver_top
% 3.81/0.96      | l1_pre_topc(sK1) != iProver_top
% 3.81/0.96      | v2_pre_topc(sK4) != iProver_top
% 3.81/0.96      | v2_pre_topc(sK1) != iProver_top ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_11564]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_12,plain,
% 3.81/0.96      ( m1_connsp_2(X0,X1,X2)
% 3.81/0.96      | ~ v3_pre_topc(X3,X1)
% 3.81/0.96      | ~ r2_hidden(X2,X3)
% 3.81/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.81/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/0.96      | ~ r1_tarski(X3,X0)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X1) ),
% 3.81/0.96      inference(cnf_transformation,[],[f79]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_4223,plain,
% 3.81/0.96      ( m1_connsp_2(X0,sK4,X1)
% 3.81/0.96      | ~ v3_pre_topc(sK6,sK4)
% 3.81/0.96      | ~ r2_hidden(X1,sK6)
% 3.81/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.81/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.81/0.96      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.81/0.96      | ~ r1_tarski(sK6,X0)
% 3.81/0.96      | v2_struct_0(sK4)
% 3.81/0.96      | ~ l1_pre_topc(sK4)
% 3.81/0.96      | ~ v2_pre_topc(sK4) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_12]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_7311,plain,
% 3.81/0.96      ( m1_connsp_2(X0,sK4,sK8)
% 3.81/0.96      | ~ v3_pre_topc(sK6,sK4)
% 3.81/0.96      | ~ r2_hidden(sK8,sK6)
% 3.81/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.81/0.96      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.81/0.96      | ~ m1_subset_1(sK8,u1_struct_0(sK4))
% 3.81/0.96      | ~ r1_tarski(sK6,X0)
% 3.81/0.96      | v2_struct_0(sK4)
% 3.81/0.96      | ~ l1_pre_topc(sK4)
% 3.81/0.96      | ~ v2_pre_topc(sK4) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_4223]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_10349,plain,
% 3.81/0.96      ( m1_connsp_2(u1_struct_0(sK3),sK4,sK8)
% 3.81/0.96      | ~ v3_pre_topc(sK6,sK4)
% 3.81/0.96      | ~ r2_hidden(sK8,sK6)
% 3.81/0.96      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.81/0.96      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.81/0.96      | ~ m1_subset_1(sK8,u1_struct_0(sK4))
% 3.81/0.96      | ~ r1_tarski(sK6,u1_struct_0(sK3))
% 3.81/0.96      | v2_struct_0(sK4)
% 3.81/0.96      | ~ l1_pre_topc(sK4)
% 3.81/0.96      | ~ v2_pre_topc(sK4) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_7311]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_10350,plain,
% 3.81/0.96      ( m1_connsp_2(u1_struct_0(sK3),sK4,sK8) = iProver_top
% 3.81/0.96      | v3_pre_topc(sK6,sK4) != iProver_top
% 3.81/0.96      | r2_hidden(sK8,sK6) != iProver_top
% 3.81/0.96      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.81/0.96      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.81/0.96      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 3.81/0.96      | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top
% 3.81/0.96      | v2_struct_0(sK4) = iProver_top
% 3.81/0.96      | l1_pre_topc(sK4) != iProver_top
% 3.81/0.96      | v2_pre_topc(sK4) != iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_10349]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_21,plain,
% 3.81/0.96      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.81/0.96      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.81/0.96      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.81/0.96      | ~ m1_connsp_2(X5,X0,X3)
% 3.81/0.96      | ~ m1_pre_topc(X4,X0)
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.81/0.96      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.81/0.96      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.81/0.96      | ~ v1_funct_1(X2)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(X4)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(X0)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X0) ),
% 3.81/0.96      inference(cnf_transformation,[],[f114]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_19,plain,
% 3.81/0.96      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.81/0.96      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.81/0.96      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.81/0.96      | ~ m1_pre_topc(X4,X0)
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.81/0.96      | ~ v1_funct_1(X2)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(X4)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(X0)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X0) ),
% 3.81/0.96      inference(cnf_transformation,[],[f112]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_237,plain,
% 3.81/0.96      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.81/0.96      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.81/0.96      | ~ r1_tmap_1(X0,X1,X2,X3)
% 3.81/0.96      | ~ m1_pre_topc(X4,X0)
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.81/0.96      | ~ v1_funct_1(X2)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(X4)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(X0)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X0) ),
% 3.81/0.96      inference(global_propositional_subsumption,
% 3.81/0.96                [status(thm)],
% 3.81/0.96                [c_21,c_19]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_238,plain,
% 3.81/0.96      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.81/0.96      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.81/0.96      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.81/0.96      | ~ m1_pre_topc(X4,X0)
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.81/0.96      | ~ v1_funct_1(X2)
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X4)
% 3.81/0.96      | ~ l1_pre_topc(X0)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X0)
% 3.81/0.96      | ~ v2_pre_topc(X1) ),
% 3.81/0.96      inference(renaming,[status(thm)],[c_237]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_728,plain,
% 3.81/0.96      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.81/0.96      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.81/0.96      | ~ m1_pre_topc(X4,X0)
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.81/0.96      | ~ v1_funct_1(X2)
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X4)
% 3.81/0.96      | ~ l1_pre_topc(X0)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X0)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.81/0.96      | sK5 != X2 ),
% 3.81/0.96      inference(resolution_lifted,[status(thm)],[c_238,c_34]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_729,plain,
% 3.81/0.96      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.81/0.96      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 3.81/0.96      | ~ m1_pre_topc(X0,X2)
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.81/0.96      | ~ v1_funct_1(sK5)
% 3.81/0.96      | v2_struct_0(X2)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | ~ l1_pre_topc(X2)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X2)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.81/0.96      inference(unflattening,[status(thm)],[c_728]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_733,plain,
% 3.81/0.96      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_pre_topc(X0,X2)
% 3.81/0.96      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 3.81/0.96      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.81/0.96      | v2_struct_0(X2)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | ~ l1_pre_topc(X2)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X2)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.81/0.96      inference(global_propositional_subsumption,
% 3.81/0.96                [status(thm)],
% 3.81/0.96                [c_729,c_35]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_734,plain,
% 3.81/0.96      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.81/0.96      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 3.81/0.96      | ~ m1_pre_topc(X0,X2)
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X2)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(X2)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X2)
% 3.81/0.96      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.81/0.96      inference(renaming,[status(thm)],[c_733]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_769,plain,
% 3.81/0.96      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.81/0.96      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 3.81/0.96      | ~ m1_pre_topc(X0,X2)
% 3.81/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X2)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(X2)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X2)
% 3.81/0.96      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.81/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_734,c_9]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3984,plain,
% 3.81/0.96      ( r1_tmap_1(X0,X1,k2_tmap_1(sK4,X1,sK5,X0),X2)
% 3.81/0.96      | ~ r1_tmap_1(sK4,X1,sK5,X2)
% 3.81/0.96      | ~ m1_pre_topc(X0,sK4)
% 3.81/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(sK4)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(sK4)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(sK4)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.81/0.96      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_769]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_5633,plain,
% 3.81/0.96      ( ~ r1_tmap_1(sK4,X0,sK5,X1)
% 3.81/0.96      | r1_tmap_1(sK3,X0,k2_tmap_1(sK4,X0,sK5,sK3),X1)
% 3.81/0.96      | ~ m1_pre_topc(sK3,sK4)
% 3.81/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(sK4)
% 3.81/0.96      | v2_struct_0(sK3)
% 3.81/0.96      | ~ l1_pre_topc(X0)
% 3.81/0.96      | ~ l1_pre_topc(sK4)
% 3.81/0.96      | ~ v2_pre_topc(X0)
% 3.81/0.96      | ~ v2_pre_topc(sK4)
% 3.81/0.96      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.81/0.96      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_3984]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_9583,plain,
% 3.81/0.96      ( ~ r1_tmap_1(sK4,X0,sK5,sK8)
% 3.81/0.96      | r1_tmap_1(sK3,X0,k2_tmap_1(sK4,X0,sK5,sK3),sK8)
% 3.81/0.96      | ~ m1_pre_topc(sK3,sK4)
% 3.81/0.96      | ~ m1_subset_1(sK8,u1_struct_0(sK3))
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 3.81/0.96      | v2_struct_0(X0)
% 3.81/0.96      | v2_struct_0(sK4)
% 3.81/0.96      | v2_struct_0(sK3)
% 3.81/0.96      | ~ l1_pre_topc(X0)
% 3.81/0.96      | ~ l1_pre_topc(sK4)
% 3.81/0.96      | ~ v2_pre_topc(X0)
% 3.81/0.96      | ~ v2_pre_topc(sK4)
% 3.81/0.96      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.81/0.96      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_5633]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_9584,plain,
% 3.81/0.96      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.81/0.96      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 3.81/0.96      | r1_tmap_1(sK4,X0,sK5,sK8) != iProver_top
% 3.81/0.96      | r1_tmap_1(sK3,X0,k2_tmap_1(sK4,X0,sK5,sK3),sK8) = iProver_top
% 3.81/0.96      | m1_pre_topc(sK3,sK4) != iProver_top
% 3.81/0.96      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 3.81/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.81/0.96      | v2_struct_0(X0) = iProver_top
% 3.81/0.96      | v2_struct_0(sK4) = iProver_top
% 3.81/0.96      | v2_struct_0(sK3) = iProver_top
% 3.81/0.96      | l1_pre_topc(X0) != iProver_top
% 3.81/0.96      | l1_pre_topc(sK4) != iProver_top
% 3.81/0.96      | v2_pre_topc(X0) != iProver_top
% 3.81/0.96      | v2_pre_topc(sK4) != iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_9583]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_9586,plain,
% 3.81/0.96      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.81/0.96      | r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
% 3.81/0.96      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK8) = iProver_top
% 3.81/0.96      | m1_pre_topc(sK3,sK4) != iProver_top
% 3.81/0.96      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 3.81/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 3.81/0.96      | v2_struct_0(sK4) = iProver_top
% 3.81/0.96      | v2_struct_0(sK1) = iProver_top
% 3.81/0.96      | v2_struct_0(sK3) = iProver_top
% 3.81/0.96      | l1_pre_topc(sK4) != iProver_top
% 3.81/0.96      | l1_pre_topc(sK1) != iProver_top
% 3.81/0.96      | v2_pre_topc(sK4) != iProver_top
% 3.81/0.96      | v2_pre_topc(sK1) != iProver_top ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_9584]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_36,negated_conjecture,
% 3.81/0.96      ( m1_pre_topc(sK4,sK2) ),
% 3.81/0.96      inference(cnf_transformation,[],[f95]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3014,plain,
% 3.81/0.96      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_32,negated_conjecture,
% 3.81/0.96      ( m1_pre_topc(sK3,sK4) ),
% 3.81/0.96      inference(cnf_transformation,[],[f99]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3016,plain,
% 3.81/0.96      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_18,plain,
% 3.81/0.96      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.81/0.96      | ~ m1_pre_topc(X1,X3)
% 3.81/0.96      | ~ m1_pre_topc(X4,X3)
% 3.81/0.96      | ~ m1_pre_topc(X4,X1)
% 3.81/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.81/0.96      | ~ v1_funct_1(X0)
% 3.81/0.96      | v2_struct_0(X3)
% 3.81/0.96      | v2_struct_0(X2)
% 3.81/0.96      | ~ l1_pre_topc(X3)
% 3.81/0.96      | ~ l1_pre_topc(X2)
% 3.81/0.96      | ~ v2_pre_topc(X3)
% 3.81/0.96      | ~ v2_pre_topc(X2)
% 3.81/0.96      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X4)) = k3_tmap_1(X3,X2,X1,X4,X0) ),
% 3.81/0.96      inference(cnf_transformation,[],[f81]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_900,plain,
% 3.81/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.81/0.96      | ~ m1_pre_topc(X2,X1)
% 3.81/0.96      | ~ m1_pre_topc(X2,X0)
% 3.81/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X4))))
% 3.81/0.96      | ~ v1_funct_1(X3)
% 3.81/0.96      | v2_struct_0(X4)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | ~ l1_pre_topc(X4)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X4)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X4),X3,u1_struct_0(X2)) = k3_tmap_1(X1,X4,X0,X2,X3)
% 3.81/0.96      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X4) != u1_struct_0(sK1)
% 3.81/0.96      | sK5 != X3 ),
% 3.81/0.96      inference(resolution_lifted,[status(thm)],[c_18,c_34]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_901,plain,
% 3.81/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.81/0.96      | ~ m1_pre_topc(X2,X0)
% 3.81/0.96      | ~ m1_pre_topc(X2,X1)
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
% 3.81/0.96      | ~ v1_funct_1(sK5)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X3)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(X3)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X3)
% 3.81/0.96      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK5,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK5)
% 3.81/0.96      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 3.81/0.96      inference(unflattening,[status(thm)],[c_900]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_22,plain,
% 3.81/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.81/0.96      | ~ m1_pre_topc(X2,X0)
% 3.81/0.96      | m1_pre_topc(X2,X1)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X1) ),
% 3.81/0.96      inference(cnf_transformation,[],[f85]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_905,plain,
% 3.81/0.96      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
% 3.81/0.96      | ~ m1_pre_topc(X0,X1)
% 3.81/0.96      | ~ m1_pre_topc(X2,X0)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X3)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(X3)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X3)
% 3.81/0.96      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK5,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK5)
% 3.81/0.96      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 3.81/0.96      inference(global_propositional_subsumption,
% 3.81/0.96                [status(thm)],
% 3.81/0.96                [c_901,c_35,c_22]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_906,plain,
% 3.81/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.81/0.96      | ~ m1_pre_topc(X2,X0)
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X3)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(X3)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X3)
% 3.81/0.96      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK5,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK5)
% 3.81/0.96      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 3.81/0.96      inference(renaming,[status(thm)],[c_905]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_2998,plain,
% 3.81/0.96      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK5)
% 3.81/0.96      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.81/0.96      | m1_pre_topc(X0,X3) != iProver_top
% 3.81/0.96      | m1_pre_topc(X2,X0) != iProver_top
% 3.81/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.81/0.96      | v2_struct_0(X3) = iProver_top
% 3.81/0.96      | v2_struct_0(X1) = iProver_top
% 3.81/0.96      | l1_pre_topc(X3) != iProver_top
% 3.81/0.96      | l1_pre_topc(X1) != iProver_top
% 3.81/0.96      | v2_pre_topc(X3) != iProver_top
% 3.81/0.96      | v2_pre_topc(X1) != iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_906]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_4099,plain,
% 3.81/0.96      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k3_tmap_1(X2,X0,sK4,X1,sK5)
% 3.81/0.96      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.81/0.96      | m1_pre_topc(X1,sK4) != iProver_top
% 3.81/0.96      | m1_pre_topc(sK4,X2) != iProver_top
% 3.81/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.81/0.96      | v2_struct_0(X0) = iProver_top
% 3.81/0.96      | v2_struct_0(X2) = iProver_top
% 3.81/0.96      | l1_pre_topc(X0) != iProver_top
% 3.81/0.96      | l1_pre_topc(X2) != iProver_top
% 3.81/0.96      | v2_pre_topc(X0) != iProver_top
% 3.81/0.96      | v2_pre_topc(X2) != iProver_top ),
% 3.81/0.96      inference(equality_resolution,[status(thm)],[c_2998]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_6558,plain,
% 3.81/0.96      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK4,X0,sK5)
% 3.81/0.96      | m1_pre_topc(X0,sK4) != iProver_top
% 3.81/0.96      | m1_pre_topc(sK4,X1) != iProver_top
% 3.81/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 3.81/0.96      | v2_struct_0(X1) = iProver_top
% 3.81/0.96      | v2_struct_0(sK1) = iProver_top
% 3.81/0.96      | l1_pre_topc(X1) != iProver_top
% 3.81/0.96      | l1_pre_topc(sK1) != iProver_top
% 3.81/0.96      | v2_pre_topc(X1) != iProver_top
% 3.81/0.96      | v2_pre_topc(sK1) != iProver_top ),
% 3.81/0.96      inference(equality_resolution,[status(thm)],[c_4099]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_45,negated_conjecture,
% 3.81/0.96      ( ~ v2_struct_0(sK1) ),
% 3.81/0.96      inference(cnf_transformation,[],[f86]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_46,plain,
% 3.81/0.96      ( v2_struct_0(sK1) != iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_44,negated_conjecture,
% 3.81/0.96      ( v2_pre_topc(sK1) ),
% 3.81/0.96      inference(cnf_transformation,[],[f87]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_47,plain,
% 3.81/0.96      ( v2_pre_topc(sK1) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_43,negated_conjecture,
% 3.81/0.96      ( l1_pre_topc(sK1) ),
% 3.81/0.96      inference(cnf_transformation,[],[f88]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_48,plain,
% 3.81/0.96      ( l1_pre_topc(sK1) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_33,negated_conjecture,
% 3.81/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
% 3.81/0.96      inference(cnf_transformation,[],[f98]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_58,plain,
% 3.81/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_8183,plain,
% 3.81/0.96      ( v2_pre_topc(X1) != iProver_top
% 3.81/0.96      | v2_struct_0(X1) = iProver_top
% 3.81/0.96      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK4,X0,sK5)
% 3.81/0.96      | m1_pre_topc(X0,sK4) != iProver_top
% 3.81/0.96      | m1_pre_topc(sK4,X1) != iProver_top
% 3.81/0.96      | l1_pre_topc(X1) != iProver_top ),
% 3.81/0.96      inference(global_propositional_subsumption,
% 3.81/0.96                [status(thm)],
% 3.81/0.96                [c_6558,c_46,c_47,c_48,c_58]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_8184,plain,
% 3.81/0.96      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK4,X0,sK5)
% 3.81/0.96      | m1_pre_topc(X0,sK4) != iProver_top
% 3.81/0.96      | m1_pre_topc(sK4,X1) != iProver_top
% 3.81/0.96      | v2_struct_0(X1) = iProver_top
% 3.81/0.96      | l1_pre_topc(X1) != iProver_top
% 3.81/0.96      | v2_pre_topc(X1) != iProver_top ),
% 3.81/0.96      inference(renaming,[status(thm)],[c_8183]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_8195,plain,
% 3.81/0.96      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK4,sK3,sK5)
% 3.81/0.96      | m1_pre_topc(sK4,X0) != iProver_top
% 3.81/0.96      | v2_struct_0(X0) = iProver_top
% 3.81/0.96      | l1_pre_topc(X0) != iProver_top
% 3.81/0.96      | v2_pre_topc(X0) != iProver_top ),
% 3.81/0.96      inference(superposition,[status(thm)],[c_3016,c_8184]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_17,plain,
% 3.81/0.96      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.81/0.96      | ~ m1_pre_topc(X3,X1)
% 3.81/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.81/0.96      | ~ v1_funct_1(X0)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X2)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(X2)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X2)
% 3.81/0.96      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.81/0.96      inference(cnf_transformation,[],[f80]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_948,plain,
% 3.81/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.81/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.81/0.96      | ~ v1_funct_1(X2)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X3)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(X3)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X3)
% 3.81/0.96      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X3) != u1_struct_0(sK1)
% 3.81/0.96      | sK5 != X2 ),
% 3.81/0.96      inference(resolution_lifted,[status(thm)],[c_17,c_34]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_949,plain,
% 3.81/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.81/0.96      | ~ v1_funct_1(sK5)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X2)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(X2)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X2)
% 3.81/0.96      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 3.81/0.96      inference(unflattening,[status(thm)],[c_948]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_953,plain,
% 3.81/0.96      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.81/0.96      | ~ m1_pre_topc(X0,X1)
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X2)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(X2)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X2)
% 3.81/0.96      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 3.81/0.96      inference(global_propositional_subsumption,
% 3.81/0.96                [status(thm)],
% 3.81/0.96                [c_949,c_35]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_954,plain,
% 3.81/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.81/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.81/0.96      | v2_struct_0(X1)
% 3.81/0.96      | v2_struct_0(X2)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ l1_pre_topc(X2)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X2)
% 3.81/0.96      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 3.81/0.96      inference(renaming,[status(thm)],[c_953]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_2997,plain,
% 3.81/0.96      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK5,X2)
% 3.81/0.96      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.81/0.96      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.81/0.96      | m1_pre_topc(X2,X0) != iProver_top
% 3.81/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.81/0.96      | v2_struct_0(X0) = iProver_top
% 3.81/0.96      | v2_struct_0(X1) = iProver_top
% 3.81/0.96      | l1_pre_topc(X0) != iProver_top
% 3.81/0.96      | l1_pre_topc(X1) != iProver_top
% 3.81/0.96      | v2_pre_topc(X0) != iProver_top
% 3.81/0.96      | v2_pre_topc(X1) != iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_954]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3597,plain,
% 3.81/0.96      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
% 3.81/0.96      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.81/0.96      | m1_pre_topc(X1,sK4) != iProver_top
% 3.81/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.81/0.96      | v2_struct_0(X0) = iProver_top
% 3.81/0.96      | v2_struct_0(sK4) = iProver_top
% 3.81/0.96      | l1_pre_topc(X0) != iProver_top
% 3.81/0.96      | l1_pre_topc(sK4) != iProver_top
% 3.81/0.96      | v2_pre_topc(X0) != iProver_top
% 3.81/0.96      | v2_pre_topc(sK4) != iProver_top ),
% 3.81/0.96      inference(equality_resolution,[status(thm)],[c_2997]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_40,negated_conjecture,
% 3.81/0.96      ( l1_pre_topc(sK2) ),
% 3.81/0.96      inference(cnf_transformation,[],[f91]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_51,plain,
% 3.81/0.96      ( l1_pre_topc(sK2) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_37,negated_conjecture,
% 3.81/0.96      ( ~ v2_struct_0(sK4) ),
% 3.81/0.96      inference(cnf_transformation,[],[f94]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_54,plain,
% 3.81/0.96      ( v2_struct_0(sK4) != iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_7,plain,
% 3.81/0.96      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.81/0.96      inference(cnf_transformation,[],[f70]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3031,plain,
% 3.81/0.96      ( m1_pre_topc(X0,X1) != iProver_top
% 3.81/0.96      | l1_pre_topc(X1) != iProver_top
% 3.81/0.96      | l1_pre_topc(X0) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_4196,plain,
% 3.81/0.96      ( l1_pre_topc(sK4) = iProver_top
% 3.81/0.96      | l1_pre_topc(sK2) != iProver_top ),
% 3.81/0.96      inference(superposition,[status(thm)],[c_3014,c_3031]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_4449,plain,
% 3.81/0.96      ( l1_pre_topc(X0) != iProver_top
% 3.81/0.96      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
% 3.81/0.96      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.81/0.96      | m1_pre_topc(X1,sK4) != iProver_top
% 3.81/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.81/0.96      | v2_struct_0(X0) = iProver_top
% 3.81/0.96      | v2_pre_topc(X0) != iProver_top
% 3.81/0.96      | v2_pre_topc(sK4) != iProver_top ),
% 3.81/0.96      inference(global_propositional_subsumption,
% 3.81/0.96                [status(thm)],
% 3.81/0.96                [c_3597,c_51,c_54,c_4196]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_4450,plain,
% 3.81/0.96      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
% 3.81/0.96      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.81/0.96      | m1_pre_topc(X1,sK4) != iProver_top
% 3.81/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.81/0.96      | v2_struct_0(X0) = iProver_top
% 3.81/0.96      | l1_pre_topc(X0) != iProver_top
% 3.81/0.96      | v2_pre_topc(X0) != iProver_top
% 3.81/0.96      | v2_pre_topc(sK4) != iProver_top ),
% 3.81/0.96      inference(renaming,[status(thm)],[c_4449]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_4463,plain,
% 3.81/0.96      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK1,sK5,X0)
% 3.81/0.96      | m1_pre_topc(X0,sK4) != iProver_top
% 3.81/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 3.81/0.96      | v2_struct_0(sK1) = iProver_top
% 3.81/0.96      | l1_pre_topc(sK1) != iProver_top
% 3.81/0.96      | v2_pre_topc(sK4) != iProver_top
% 3.81/0.96      | v2_pre_topc(sK1) != iProver_top ),
% 3.81/0.96      inference(equality_resolution,[status(thm)],[c_4450]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_41,negated_conjecture,
% 3.81/0.96      ( v2_pre_topc(sK2) ),
% 3.81/0.96      inference(cnf_transformation,[],[f90]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_50,plain,
% 3.81/0.96      ( v2_pre_topc(sK2) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_6,plain,
% 3.81/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.81/0.96      | ~ l1_pre_topc(X1)
% 3.81/0.96      | ~ v2_pre_topc(X1)
% 3.81/0.96      | v2_pre_topc(X0) ),
% 3.81/0.96      inference(cnf_transformation,[],[f69]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3032,plain,
% 3.81/0.96      ( m1_pre_topc(X0,X1) != iProver_top
% 3.81/0.96      | l1_pre_topc(X1) != iProver_top
% 3.81/0.96      | v2_pre_topc(X1) != iProver_top
% 3.81/0.96      | v2_pre_topc(X0) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_4648,plain,
% 3.81/0.96      ( l1_pre_topc(sK2) != iProver_top
% 3.81/0.96      | v2_pre_topc(sK4) = iProver_top
% 3.81/0.96      | v2_pre_topc(sK2) != iProver_top ),
% 3.81/0.96      inference(superposition,[status(thm)],[c_3014,c_3032]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_7449,plain,
% 3.81/0.96      ( m1_pre_topc(X0,sK4) != iProver_top
% 3.81/0.96      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK1,sK5,X0) ),
% 3.81/0.96      inference(global_propositional_subsumption,
% 3.81/0.96                [status(thm)],
% 3.81/0.96                [c_4463,c_46,c_47,c_48,c_50,c_51,c_58,c_4648]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_7450,plain,
% 3.81/0.96      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK1,sK5,X0)
% 3.81/0.96      | m1_pre_topc(X0,sK4) != iProver_top ),
% 3.81/0.96      inference(renaming,[status(thm)],[c_7449]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_7457,plain,
% 3.81/0.96      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK1,sK5,sK3) ),
% 3.81/0.96      inference(superposition,[status(thm)],[c_3016,c_7450]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_8196,plain,
% 3.81/0.96      ( k3_tmap_1(X0,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3)
% 3.81/0.96      | m1_pre_topc(sK4,X0) != iProver_top
% 3.81/0.96      | v2_struct_0(X0) = iProver_top
% 3.81/0.96      | l1_pre_topc(X0) != iProver_top
% 3.81/0.96      | v2_pre_topc(X0) != iProver_top ),
% 3.81/0.96      inference(light_normalisation,[status(thm)],[c_8195,c_7457]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_8206,plain,
% 3.81/0.96      ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3)
% 3.81/0.96      | v2_struct_0(sK2) = iProver_top
% 3.81/0.96      | l1_pre_topc(sK2) != iProver_top
% 3.81/0.96      | v2_pre_topc(sK2) != iProver_top ),
% 3.81/0.96      inference(superposition,[status(thm)],[c_3014,c_8196]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_42,negated_conjecture,
% 3.81/0.96      ( ~ v2_struct_0(sK2) ),
% 3.81/0.96      inference(cnf_transformation,[],[f89]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_49,plain,
% 3.81/0.96      ( v2_struct_0(sK2) != iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_8445,plain,
% 3.81/0.96      ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3) ),
% 3.81/0.96      inference(global_propositional_subsumption,
% 3.81/0.96                [status(thm)],
% 3.81/0.96                [c_8206,c_49,c_50,c_51]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_23,negated_conjecture,
% 3.81/0.96      ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
% 3.81/0.96      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
% 3.81/0.96      inference(cnf_transformation,[],[f108]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3024,plain,
% 3.81/0.96      ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 3.81/0.96      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_25,negated_conjecture,
% 3.81/0.96      ( sK7 = sK8 ),
% 3.81/0.96      inference(cnf_transformation,[],[f106]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3111,plain,
% 3.81/0.96      ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
% 3.81/0.96      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 3.81/0.96      inference(light_normalisation,[status(thm)],[c_3024,c_25]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_8449,plain,
% 3.81/0.96      ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
% 3.81/0.96      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK8) != iProver_top ),
% 3.81/0.96      inference(demodulation,[status(thm)],[c_8445,c_3111]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_24,negated_conjecture,
% 3.81/0.96      ( r1_tmap_1(sK4,sK1,sK5,sK7)
% 3.81/0.96      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
% 3.81/0.96      inference(cnf_transformation,[],[f107]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3023,plain,
% 3.81/0.96      ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
% 3.81/0.96      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3100,plain,
% 3.81/0.96      ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
% 3.81/0.96      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
% 3.81/0.96      inference(light_normalisation,[status(thm)],[c_3023,c_25]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_8448,plain,
% 3.81/0.96      ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
% 3.81/0.96      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK8) = iProver_top ),
% 3.81/0.96      inference(demodulation,[status(thm)],[c_8445,c_3100]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_8,plain,
% 3.81/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.81/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.81/0.96      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/0.96      | ~ l1_pre_topc(X1) ),
% 3.81/0.96      inference(cnf_transformation,[],[f71]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3484,plain,
% 3.81/0.96      ( ~ m1_pre_topc(sK3,sK4)
% 3.81/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.81/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.96      | ~ l1_pre_topc(sK4) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_8]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_6984,plain,
% 3.81/0.96      ( ~ m1_pre_topc(sK3,sK4)
% 3.81/0.96      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.81/0.96      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.96      | ~ l1_pre_topc(sK4) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_3484]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_6985,plain,
% 3.81/0.96      ( m1_pre_topc(sK3,sK4) != iProver_top
% 3.81/0.96      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.81/0.96      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.81/0.96      | l1_pre_topc(sK4) != iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_6984]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_1,plain,
% 3.81/0.96      ( r1_tarski(X0,X0) ),
% 3.81/0.96      inference(cnf_transformation,[],[f109]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_5677,plain,
% 3.81/0.96      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_1]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_5680,plain,
% 3.81/0.96      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_5677]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3,plain,
% 3.81/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.81/0.96      inference(cnf_transformation,[],[f67]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_4837,plain,
% 3.81/0.96      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.96      | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_3]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_5676,plain,
% 3.81/0.96      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.96      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_4837]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_5678,plain,
% 3.81/0.96      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.81/0.96      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_5676]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_4842,plain,
% 3.81/0.96      ( ~ m1_pre_topc(sK3,sK4)
% 3.81/0.96      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.81/0.96      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.96      | ~ l1_pre_topc(sK4) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_3484]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_4843,plain,
% 3.81/0.96      ( m1_pre_topc(sK3,sK4) != iProver_top
% 3.81/0.96      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.81/0.96      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.81/0.96      | l1_pre_topc(sK4) != iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_4842]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3662,plain,
% 3.81/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(X0)) | ~ r1_tarski(sK6,X0) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_3]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_4017,plain,
% 3.81/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.96      | ~ r1_tarski(sK6,u1_struct_0(sK3)) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_3662]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_4018,plain,
% 3.81/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.81/0.96      | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_4017]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_10,plain,
% 3.81/0.96      ( ~ v3_pre_topc(X0,X1)
% 3.81/0.96      | v3_pre_topc(X0,X2)
% 3.81/0.96      | ~ m1_pre_topc(X2,X1)
% 3.81/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.81/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/0.96      | ~ l1_pre_topc(X1) ),
% 3.81/0.96      inference(cnf_transformation,[],[f111]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3603,plain,
% 3.81/0.96      ( v3_pre_topc(sK6,X0)
% 3.81/0.96      | ~ v3_pre_topc(sK6,sK2)
% 3.81/0.96      | ~ m1_pre_topc(X0,sK2)
% 3.81/0.96      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.81/0.96      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.81/0.96      | ~ l1_pre_topc(sK2) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_10]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3869,plain,
% 3.81/0.96      ( v3_pre_topc(sK6,sK4)
% 3.81/0.96      | ~ v3_pre_topc(sK6,sK2)
% 3.81/0.96      | ~ m1_pre_topc(sK4,sK2)
% 3.81/0.96      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.81/0.96      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.81/0.96      | ~ l1_pre_topc(sK2) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_3603]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3870,plain,
% 3.81/0.96      ( v3_pre_topc(sK6,sK4) = iProver_top
% 3.81/0.96      | v3_pre_topc(sK6,sK2) != iProver_top
% 3.81/0.96      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.81/0.96      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.81/0.96      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.81/0.96      | l1_pre_topc(sK2) != iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_3869]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_1993,plain,( X0 = X0 ),theory(equality) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3454,plain,
% 3.81/0.96      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_1993]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_30,negated_conjecture,
% 3.81/0.96      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 3.81/0.96      inference(cnf_transformation,[],[f101]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3018,plain,
% 3.81/0.96      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3069,plain,
% 3.81/0.96      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 3.81/0.96      inference(light_normalisation,[status(thm)],[c_3018,c_25]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_27,negated_conjecture,
% 3.81/0.96      ( r2_hidden(sK7,sK6) ),
% 3.81/0.96      inference(cnf_transformation,[],[f104]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3021,plain,
% 3.81/0.96      ( r2_hidden(sK7,sK6) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_3064,plain,
% 3.81/0.96      ( r2_hidden(sK8,sK6) = iProver_top ),
% 3.81/0.96      inference(light_normalisation,[status(thm)],[c_3021,c_25]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_2002,plain,
% 3.81/0.96      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.81/0.96      theory(equality) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_2017,plain,
% 3.81/0.96      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_2002]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_0,plain,
% 3.81/0.96      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.81/0.96      inference(cnf_transformation,[],[f65]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_121,plain,
% 3.81/0.96      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_0]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_2,plain,
% 3.81/0.96      ( r1_tarski(X0,X0) ),
% 3.81/0.96      inference(cnf_transformation,[],[f110]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_117,plain,
% 3.81/0.96      ( r1_tarski(sK1,sK1) ),
% 3.81/0.96      inference(instantiation,[status(thm)],[c_2]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_26,negated_conjecture,
% 3.81/0.96      ( r1_tarski(sK6,u1_struct_0(sK3)) ),
% 3.81/0.96      inference(cnf_transformation,[],[f105]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_65,plain,
% 3.81/0.96      ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_28,negated_conjecture,
% 3.81/0.96      ( v3_pre_topc(sK6,sK2) ),
% 3.81/0.96      inference(cnf_transformation,[],[f103]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_63,plain,
% 3.81/0.96      ( v3_pre_topc(sK6,sK2) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_29,negated_conjecture,
% 3.81/0.96      ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
% 3.81/0.96      inference(cnf_transformation,[],[f102]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_62,plain,
% 3.81/0.96      ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_31,negated_conjecture,
% 3.81/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.81/0.96      inference(cnf_transformation,[],[f100]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_60,plain,
% 3.81/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_59,plain,
% 3.81/0.96      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_55,plain,
% 3.81/0.96      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_39,negated_conjecture,
% 3.81/0.96      ( ~ v2_struct_0(sK3) ),
% 3.81/0.96      inference(cnf_transformation,[],[f92]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(c_52,plain,
% 3.81/0.96      ( v2_struct_0(sK3) != iProver_top ),
% 3.81/0.96      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.81/0.96  
% 3.81/0.96  cnf(contradiction,plain,
% 3.81/0.96      ( $false ),
% 3.81/0.96      inference(minisat,
% 3.81/0.96                [status(thm)],
% 3.81/0.96                [c_11566,c_10350,c_9586,c_8449,c_8448,c_6985,c_5680,
% 3.81/0.96                 c_5678,c_4843,c_4648,c_4196,c_4018,c_3870,c_3454,c_3069,
% 3.81/0.96                 c_3064,c_2017,c_121,c_117,c_65,c_63,c_62,c_60,c_59,c_58,
% 3.81/0.96                 c_55,c_54,c_52,c_51,c_50,c_48,c_47,c_46]) ).
% 3.81/0.96  
% 3.81/0.96  
% 3.81/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.81/0.96  
% 3.81/0.96  ------                               Statistics
% 3.81/0.96  
% 3.81/0.96  ------ General
% 3.81/0.96  
% 3.81/0.96  abstr_ref_over_cycles:                  0
% 3.81/0.96  abstr_ref_under_cycles:                 0
% 3.81/0.96  gc_basic_clause_elim:                   0
% 3.81/0.96  forced_gc_time:                         0
% 3.81/0.96  parsing_time:                           0.016
% 3.81/0.96  unif_index_cands_time:                  0.
% 3.81/0.96  unif_index_add_time:                    0.
% 3.81/0.96  orderings_time:                         0.
% 3.81/0.96  out_proof_time:                         0.018
% 3.81/0.96  total_time:                             0.326
% 3.81/0.96  num_of_symbols:                         58
% 3.81/0.96  num_of_terms:                           5595
% 3.81/0.96  
% 3.81/0.96  ------ Preprocessing
% 3.81/0.96  
% 3.81/0.96  num_of_splits:                          0
% 3.81/0.96  num_of_split_atoms:                     0
% 3.81/0.96  num_of_reused_defs:                     0
% 3.81/0.96  num_eq_ax_congr_red:                    29
% 3.81/0.96  num_of_sem_filtered_clauses:            1
% 3.81/0.96  num_of_subtypes:                        0
% 3.81/0.96  monotx_restored_types:                  0
% 3.81/0.96  sat_num_of_epr_types:                   0
% 3.81/0.96  sat_num_of_non_cyclic_types:            0
% 3.81/0.96  sat_guarded_non_collapsed_types:        0
% 3.81/0.96  num_pure_diseq_elim:                    0
% 3.81/0.96  simp_replaced_by:                       0
% 3.81/0.96  res_preprocessed:                       206
% 3.81/0.96  prep_upred:                             0
% 3.81/0.96  prep_unflattend:                        27
% 3.81/0.96  smt_new_axioms:                         0
% 3.81/0.96  pred_elim_cands:                        10
% 3.81/0.96  pred_elim:                              2
% 3.81/0.96  pred_elim_cl:                           3
% 3.81/0.96  pred_elim_cycles:                       6
% 3.81/0.96  merged_defs:                            16
% 3.81/0.96  merged_defs_ncl:                        0
% 3.81/0.96  bin_hyper_res:                          16
% 3.81/0.96  prep_cycles:                            4
% 3.81/0.96  pred_elim_time:                         0.03
% 3.81/0.96  splitting_time:                         0.
% 3.81/0.96  sem_filter_time:                        0.
% 3.81/0.96  monotx_time:                            0.001
% 3.81/0.96  subtype_inf_time:                       0.
% 3.81/0.96  
% 3.81/0.96  ------ Problem properties
% 3.81/0.96  
% 3.81/0.96  clauses:                                42
% 3.81/0.96  conjectures:                            21
% 3.81/0.96  epr:                                    19
% 3.81/0.96  horn:                                   30
% 3.81/0.96  ground:                                 21
% 3.81/0.96  unary:                                  20
% 3.81/0.96  binary:                                 4
% 3.81/0.96  lits:                                   156
% 3.81/0.96  lits_eq:                                12
% 3.81/0.96  fd_pure:                                0
% 3.81/0.96  fd_pseudo:                              0
% 3.81/0.96  fd_cond:                                0
% 3.81/0.96  fd_pseudo_cond:                         1
% 3.81/0.96  ac_symbols:                             0
% 3.81/0.96  
% 3.81/0.96  ------ Propositional Solver
% 3.81/0.96  
% 3.81/0.96  prop_solver_calls:                      29
% 3.81/0.96  prop_fast_solver_calls:                 2777
% 3.81/0.96  smt_solver_calls:                       0
% 3.81/0.96  smt_fast_solver_calls:                  0
% 3.81/0.96  prop_num_of_clauses:                    3382
% 3.81/0.96  prop_preprocess_simplified:             8626
% 3.81/0.96  prop_fo_subsumed:                       103
% 3.81/0.96  prop_solver_time:                       0.
% 3.81/0.96  smt_solver_time:                        0.
% 3.81/0.96  smt_fast_solver_time:                   0.
% 3.81/0.96  prop_fast_solver_time:                  0.
% 3.81/0.96  prop_unsat_core_time:                   0.
% 3.81/0.96  
% 3.81/0.96  ------ QBF
% 3.81/0.96  
% 3.81/0.96  qbf_q_res:                              0
% 3.81/0.96  qbf_num_tautologies:                    0
% 3.81/0.96  qbf_prep_cycles:                        0
% 3.81/0.96  
% 3.81/0.96  ------ BMC1
% 3.81/0.96  
% 3.81/0.96  bmc1_current_bound:                     -1
% 3.81/0.96  bmc1_last_solved_bound:                 -1
% 3.81/0.96  bmc1_unsat_core_size:                   -1
% 3.81/0.96  bmc1_unsat_core_parents_size:           -1
% 3.81/0.96  bmc1_merge_next_fun:                    0
% 3.81/0.96  bmc1_unsat_core_clauses_time:           0.
% 3.81/0.96  
% 3.81/0.96  ------ Instantiation
% 3.81/0.96  
% 3.81/0.96  inst_num_of_clauses:                    898
% 3.81/0.96  inst_num_in_passive:                    230
% 3.81/0.96  inst_num_in_active:                     654
% 3.81/0.96  inst_num_in_unprocessed:                13
% 3.81/0.96  inst_num_of_loops:                      732
% 3.81/0.96  inst_num_of_learning_restarts:          0
% 3.81/0.96  inst_num_moves_active_passive:          71
% 3.81/0.96  inst_lit_activity:                      0
% 3.81/0.96  inst_lit_activity_moves:                0
% 3.81/0.96  inst_num_tautologies:                   0
% 3.81/0.96  inst_num_prop_implied:                  0
% 3.81/0.96  inst_num_existing_simplified:           0
% 3.81/0.96  inst_num_eq_res_simplified:             0
% 3.81/0.96  inst_num_child_elim:                    0
% 3.81/0.96  inst_num_of_dismatching_blockings:      322
% 3.81/0.96  inst_num_of_non_proper_insts:           1533
% 3.81/0.96  inst_num_of_duplicates:                 0
% 3.81/0.96  inst_inst_num_from_inst_to_res:         0
% 3.81/0.96  inst_dismatching_checking_time:         0.
% 3.81/0.96  
% 3.81/0.96  ------ Resolution
% 3.81/0.96  
% 3.81/0.96  res_num_of_clauses:                     0
% 3.81/0.96  res_num_in_passive:                     0
% 3.81/0.96  res_num_in_active:                      0
% 3.81/0.96  res_num_of_loops:                       210
% 3.81/0.96  res_forward_subset_subsumed:            221
% 3.81/0.96  res_backward_subset_subsumed:           12
% 3.81/0.96  res_forward_subsumed:                   0
% 3.81/0.96  res_backward_subsumed:                  0
% 3.81/0.96  res_forward_subsumption_resolution:     9
% 3.81/0.96  res_backward_subsumption_resolution:    0
% 3.81/0.96  res_clause_to_clause_subsumption:       969
% 3.81/0.96  res_orphan_elimination:                 0
% 3.81/0.96  res_tautology_del:                      175
% 3.81/0.96  res_num_eq_res_simplified:              0
% 3.81/0.96  res_num_sel_changes:                    0
% 3.81/0.96  res_moves_from_active_to_pass:          0
% 3.81/0.96  
% 3.81/0.96  ------ Superposition
% 3.81/0.96  
% 3.81/0.96  sup_time_total:                         0.
% 3.81/0.96  sup_time_generating:                    0.
% 3.81/0.96  sup_time_sim_full:                      0.
% 3.81/0.96  sup_time_sim_immed:                     0.
% 3.81/0.96  
% 3.81/0.96  sup_num_of_clauses:                     204
% 3.81/0.96  sup_num_in_active:                      144
% 3.81/0.96  sup_num_in_passive:                     60
% 3.81/0.96  sup_num_of_loops:                       146
% 3.81/0.96  sup_fw_superposition:                   157
% 3.81/0.96  sup_bw_superposition:                   107
% 3.81/0.96  sup_immediate_simplified:               46
% 3.81/0.96  sup_given_eliminated:                   0
% 3.81/0.96  comparisons_done:                       0
% 3.81/0.96  comparisons_avoided:                    0
% 3.81/0.96  
% 3.81/0.96  ------ Simplifications
% 3.81/0.96  
% 3.81/0.96  
% 3.81/0.96  sim_fw_subset_subsumed:                 31
% 3.81/0.96  sim_bw_subset_subsumed:                 0
% 3.81/0.96  sim_fw_subsumed:                        9
% 3.81/0.96  sim_bw_subsumed:                        5
% 3.81/0.96  sim_fw_subsumption_res:                 6
% 3.81/0.96  sim_bw_subsumption_res:                 0
% 3.81/0.96  sim_tautology_del:                      2
% 3.81/0.96  sim_eq_tautology_del:                   9
% 3.81/0.96  sim_eq_res_simp:                        0
% 3.81/0.96  sim_fw_demodulated:                     0
% 3.81/0.96  sim_bw_demodulated:                     2
% 3.81/0.96  sim_light_normalised:                   5
% 3.81/0.96  sim_joinable_taut:                      0
% 3.81/0.96  sim_joinable_simp:                      0
% 3.81/0.96  sim_ac_normalised:                      0
% 3.81/0.96  sim_smt_subsumption:                    0
% 3.81/0.96  
%------------------------------------------------------------------------------
