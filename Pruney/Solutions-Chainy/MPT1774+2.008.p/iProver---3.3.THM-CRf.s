%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:13 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  242 ( 899 expanded)
%              Number of clauses        :  160 ( 204 expanded)
%              Number of leaves         :   24 ( 382 expanded)
%              Depth                    :   21
%              Number of atoms          : 1805 (18133 expanded)
%              Number of equality atoms :  335 (1234 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal clause size      :   50 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f28,plain,(
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
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
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
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
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
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
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
    inference(flattening,[],[f28])).

fof(f35,plain,(
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
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
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
    inference(nnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | X5 != X6
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X5,X4)
      | ~ v3_pre_topc(X4,X1)
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
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X6,X4)
      | ~ v3_pre_topc(X4,X1)
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
    inference(equality_resolution,[],[f58])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f37,f45,f44,f43,f42,f41,f40,f39,f38])).

fof(f78,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | X5 != X6
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X5,X4)
      | ~ v3_pre_topc(X4,X1)
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
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X6,X4)
      | ~ v3_pre_topc(X4,X1)
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
    inference(equality_resolution,[],[f57])).

fof(f7,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f46])).

fof(f82,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,(
    v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f66,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f65,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f64,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f63,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1150,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,X0_54,X1_54)
    | r1_tmap_1(X0_53,X1_53,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_2711,plain,
    ( r1_tmap_1(sK2,sK0,X0_54,X1_54)
    | ~ r1_tmap_1(sK2,sK0,X2_54,sK6)
    | X0_54 != X2_54
    | X1_54 != sK6 ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_3114,plain,
    ( ~ r1_tmap_1(sK2,sK0,X0_54,sK6)
    | r1_tmap_1(sK2,sK0,X1_54,sK7)
    | X1_54 != X0_54
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_2711])).

cnf(c_6289,plain,
    ( r1_tmap_1(sK2,sK0,X0_54,sK7)
    | ~ r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | X0_54 != k2_tmap_1(sK3,sK0,sK4,sK2)
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_3114])).

cnf(c_6873,plain,
    ( r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK7)
    | ~ r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) != k2_tmap_1(sK3,sK0,sK4,sK2)
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_6289])).

cnf(c_6874,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) != k2_tmap_1(sK3,sK0,sK4,sK2)
    | sK7 != sK6
    | r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK7) = iProver_top
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6873])).

cnf(c_2341,plain,
    ( r1_tmap_1(sK2,sK0,X0_54,X1_54)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | X0_54 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | X1_54 != sK7 ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_2531,plain,
    ( r1_tmap_1(sK2,sK0,X0_54,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | X0_54 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2341])).

cnf(c_6429,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | k2_tmap_1(sK3,sK0,sK4,sK2) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2531])).

cnf(c_6433,plain,
    ( k2_tmap_1(sK3,sK0,sK4,sK2) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK6 != sK7
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6429])).

cnf(c_1141,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_3050,plain,
    ( X0_54 != X1_54
    | X0_54 = k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != X1_54 ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_4376,plain,
    ( X0_54 = k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | X0_54 != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3050])).

cnf(c_6065,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | k2_tmap_1(sK3,sK0,sK4,sK2) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | k2_tmap_1(sK3,sK0,sK4,sK2) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4376])).

cnf(c_1140,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_5627,plain,
    ( k2_tmap_1(sK3,sK0,sK4,sK2) = k2_tmap_1(sK3,sK0,sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_4753,plain,
    ( X0_54 != X1_54
    | X0_54 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) != X1_54 ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_5392,plain,
    ( X0_54 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | X0_54 != k2_tmap_1(sK3,sK0,sK4,sK2)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) != k2_tmap_1(sK3,sK0,sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_4753])).

cnf(c_5626,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) != k2_tmap_1(sK3,sK0,sK4,sK2)
    | k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | k2_tmap_1(sK3,sK0,sK4,sK2) != k2_tmap_1(sK3,sK0,sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_5392])).

cnf(c_4367,plain,
    ( r1_tmap_1(sK2,sK0,X0_54,X1_54)
    | ~ r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK7)
    | X0_54 != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | X1_54 != sK7 ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_4974,plain,
    ( r1_tmap_1(sK2,sK0,X0_54,sK7)
    | ~ r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK7)
    | X0_54 != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_4367])).

cnf(c_5276,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK7)
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_4974])).

cnf(c_5277,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | sK7 != sK7
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top
    | r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5276])).

cnf(c_10,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X5,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ r2_hidden(X3,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_519,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X5,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | sK5 != X5
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_520,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_448,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | sK5 != X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_17])).

cnf(c_449,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | m1_subset_1(sK6,X0) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_542,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_520,c_449])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_679,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_542,c_24])).

cnf(c_680,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | r1_tmap_1(X2,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_684,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X0,X2)
    | ~ v3_pre_topc(sK5,X2)
    | r1_tmap_1(X2,X1,sK4,sK6)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_680,c_25])).

cnf(c_685,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | r1_tmap_1(X2,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_684])).

cnf(c_1107,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,sK4,X0_53),sK6)
    | r1_tmap_1(X2_53,X1_53,sK4,sK6)
    | ~ v3_pre_topc(sK5,X2_53)
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2_53)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | ~ r1_tarski(sK5,u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X2_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_685])).

cnf(c_2661,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK3,X1_53,sK4,X0_53),sK6)
    | r1_tmap_1(sK3,X1_53,sK4,sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(X0_53,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
    | ~ r1_tarski(sK5,u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1107])).

cnf(c_4357,plain,
    ( r1_tmap_1(sK3,X0_53,sK4,sK6)
    | ~ r1_tmap_1(sK2,X0_53,k2_tmap_1(sK3,X0_53,sK4,sK2),sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2661])).

cnf(c_4358,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(sK3,X0_53,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,X0_53,k2_tmap_1(sK3,X0_53,sK4,sK2),sK6) != iProver_top
    | v3_pre_topc(sK5,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53)))) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4357])).

cnf(c_4360,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) != iProver_top
    | v3_pre_topc(sK5,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4358])).

cnf(c_3362,plain,
    ( X0_54 != X1_54
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != X1_54
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = X0_54 ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_3677,plain,
    ( X0_54 != k3_tmap_1(sK1,sK0,sK3,sK2,X1_54)
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = X0_54
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,X1_54) ),
    inference(instantiation,[status(thm)],[c_3362])).

cnf(c_4018,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_3677])).

cnf(c_11,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X5,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ r2_hidden(X3,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_460,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X5,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | sK5 != X5
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_461,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK6)
    | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_483,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK6)
    | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_461,c_449])).

cnf(c_742,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK6)
    | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_483,c_24])).

cnf(c_743,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | ~ r1_tmap_1(X2,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_742])).

cnf(c_747,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X0,X2)
    | ~ v3_pre_topc(sK5,X2)
    | ~ r1_tmap_1(X2,X1,sK4,sK6)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_743,c_25])).

cnf(c_748,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | ~ r1_tmap_1(X2,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_747])).

cnf(c_1106,plain,
    ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,sK4,X0_53),sK6)
    | ~ r1_tmap_1(X2_53,X1_53,sK4,sK6)
    | ~ v3_pre_topc(sK5,X2_53)
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2_53)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | ~ r1_tarski(sK5,u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X2_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_748])).

cnf(c_2662,plain,
    ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK3,X1_53,sK4,X0_53),sK6)
    | ~ r1_tmap_1(sK3,X1_53,sK4,sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(X0_53,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
    | ~ r1_tarski(sK5,u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1106])).

cnf(c_3874,plain,
    ( ~ r1_tmap_1(sK3,X0_53,sK4,sK6)
    | r1_tmap_1(sK2,X0_53,k2_tmap_1(sK3,X0_53,sK4,sK2),sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2662])).

cnf(c_3875,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(sK3,X0_53,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,X0_53,k2_tmap_1(sK3,X0_53,sK4,sK2),sK6) = iProver_top
    | v3_pre_topc(sK5,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53)))) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3874])).

cnf(c_3877,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) = iProver_top
    | v3_pre_topc(sK5,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3875])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_634,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_24])).

cnf(c_635,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_639,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_635,c_25])).

cnf(c_640,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_639])).

cnf(c_1108,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X2_53))))
    | v2_struct_0(X2_53)
    | v2_struct_0(X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | k2_partfun1(u1_struct_0(X1_53),u1_struct_0(X2_53),sK4,u1_struct_0(X0_53)) = k2_tmap_1(X1_53,X2_53,sK4,X0_53)
    | u1_struct_0(X1_53) != u1_struct_0(sK3)
    | u1_struct_0(X2_53) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_640])).

cnf(c_2249,plain,
    ( ~ m1_pre_topc(X0_53,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(sK3)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1_53),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK3,X1_53,sK4,X0_53)
    | u1_struct_0(X1_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1108])).

cnf(c_3481,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK3)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0_53),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,X0_53,sK4,sK2)
    | u1_struct_0(X0_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2249])).

cnf(c_3483,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK0,sK4,sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3481])).

cnf(c_3446,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_1,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1137,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ r1_tarski(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3427,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(sK5,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1137])).

cnf(c_3428,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r1_tarski(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3427])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1138,plain,
    ( ~ r1_tarski(X0_54,X1_54)
    | ~ r1_tarski(X2_54,X0_54)
    | r1_tarski(X2_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3009,plain,
    ( r1_tarski(X0_54,u1_struct_0(sK3))
    | ~ r1_tarski(X0_54,u1_struct_0(sK2))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1138])).

cnf(c_3291,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | r1_tarski(sK5,u1_struct_0(sK3))
    | ~ r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3009])).

cnf(c_3292,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK3)) = iProver_top
    | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3291])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1135,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v2_pre_topc(X1_53)
    | v2_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2998,plain,
    ( ~ m1_pre_topc(sK3,X0_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X0_53)
    | v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1135])).

cnf(c_3086,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2998])).

cnf(c_3087,plain,
    ( m1_pre_topc(sK3,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3086])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X4)) = k3_tmap_1(X3,X2,X1,X4,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_583,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X4))))
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X4),X3,u1_struct_0(X2)) = k3_tmap_1(X1,X4,X0,X2,X3)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X4) != u1_struct_0(sK0)
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_584,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_588,plain,
    ( v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_25])).

cnf(c_589,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_588])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_620,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_589,c_12])).

cnf(c_1109,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_pre_topc(X1_53,X2_53)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X3_53))))
    | v2_struct_0(X2_53)
    | v2_struct_0(X3_53)
    | ~ l1_pre_topc(X2_53)
    | ~ l1_pre_topc(X3_53)
    | ~ v2_pre_topc(X2_53)
    | ~ v2_pre_topc(X3_53)
    | k2_partfun1(u1_struct_0(X1_53),u1_struct_0(X3_53),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X2_53,X3_53,X1_53,X0_53,sK4)
    | u1_struct_0(X1_53) != u1_struct_0(sK3)
    | u1_struct_0(X3_53) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_620])).

cnf(c_2248,plain,
    ( ~ m1_pre_topc(X0_53,sK3)
    | ~ m1_pre_topc(sK3,X1_53)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2_53))))
    | v2_struct_0(X2_53)
    | v2_struct_0(X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X2_53),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,X2_53,sK3,X0_53,sK4)
    | u1_struct_0(X2_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_2656,plain,
    ( ~ m1_pre_topc(sK3,X0_53)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X0_53)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1_53),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0_53,X1_53,sK3,sK2,sK4)
    | u1_struct_0(X1_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2248])).

cnf(c_3064,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK1)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0_53),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK1,X0_53,sK3,sK2,sK4)
    | u1_struct_0(X0_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2656])).

cnf(c_3066,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3064])).

cnf(c_1149,plain,
    ( X0_54 != X1_54
    | k3_tmap_1(X0_53,X1_53,X2_53,X3_53,X0_54) = k3_tmap_1(X0_53,X1_53,X2_53,X3_53,X1_54) ),
    theory(equality)).

cnf(c_3053,plain,
    ( X0_54 != sK4
    | k3_tmap_1(sK1,sK0,sK3,sK2,X0_54) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_3056,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3053])).

cnf(c_2513,plain,
    ( X0_54 != X1_54
    | X0_54 = sK6
    | sK6 != X1_54 ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_2788,plain,
    ( X0_54 = sK6
    | X0_54 != sK7
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2513])).

cnf(c_3007,plain,
    ( sK6 != sK7
    | sK7 = sK6
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2788])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1134,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2477,plain,
    ( ~ m1_pre_topc(sK3,X0_53)
    | ~ l1_pre_topc(X0_53)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_2746,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2477])).

cnf(c_2747,plain,
    ( m1_pre_topc(sK3,sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2746])).

cnf(c_2500,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_6,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1133,plain,
    ( ~ v3_pre_topc(X0_54,X0_53)
    | v3_pre_topc(X0_54,X1_53)
    | ~ m1_pre_topc(X1_53,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X1_53)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2336,plain,
    ( v3_pre_topc(sK5,X0_53)
    | ~ v3_pre_topc(sK5,sK1)
    | ~ m1_pre_topc(X0_53,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1133])).

cnf(c_2470,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ v3_pre_topc(sK5,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2336])).

cnf(c_2471,plain,
    ( v3_pre_topc(sK5,sK3) = iProver_top
    | v3_pre_topc(sK5,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2470])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1136,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | r1_tarski(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2380,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1136])).

cnf(c_2381,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2380])).

cnf(c_1110,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0_54))
    | m1_subset_1(sK6,X0_54) ),
    inference(subtyping,[status(esa)],[c_449])).

cnf(c_2371,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_2372,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2371])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1132,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53)))
    | ~ l1_pre_topc(X1_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2271,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1132])).

cnf(c_2272,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2271])).

cnf(c_2264,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1137])).

cnf(c_2265,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2264])).

cnf(c_2247,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_15,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1128,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1161,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_57,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_56,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_55,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,negated_conjecture,
    ( v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_53,plain,
    ( v3_pre_topc(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_50,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_49,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_48,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_45,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_44,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_42,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_41,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_40,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_38,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_37,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_36,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6874,c_6433,c_6065,c_5627,c_5626,c_5277,c_4360,c_4018,c_3877,c_3483,c_3446,c_3428,c_3292,c_3087,c_3086,c_3066,c_3056,c_3007,c_2747,c_2746,c_2500,c_2471,c_2381,c_2372,c_2272,c_2265,c_2247,c_1128,c_1161,c_57,c_56,c_55,c_53,c_50,c_49,c_22,c_48,c_23,c_45,c_26,c_44,c_27,c_42,c_41,c_30,c_40,c_31,c_32,c_38,c_33,c_37,c_34,c_36,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.11/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.11/0.99  
% 3.11/0.99  ------  iProver source info
% 3.11/0.99  
% 3.11/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.11/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.11/0.99  git: non_committed_changes: false
% 3.11/0.99  git: last_make_outside_of_git: false
% 3.11/0.99  
% 3.11/0.99  ------ 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options
% 3.11/0.99  
% 3.11/0.99  --out_options                           all
% 3.11/0.99  --tptp_safe_out                         true
% 3.11/0.99  --problem_path                          ""
% 3.11/0.99  --include_path                          ""
% 3.11/0.99  --clausifier                            res/vclausify_rel
% 3.11/0.99  --clausifier_options                    --mode clausify
% 3.11/0.99  --stdin                                 false
% 3.11/0.99  --stats_out                             all
% 3.11/0.99  
% 3.11/0.99  ------ General Options
% 3.11/0.99  
% 3.11/0.99  --fof                                   false
% 3.11/0.99  --time_out_real                         305.
% 3.11/0.99  --time_out_virtual                      -1.
% 3.11/0.99  --symbol_type_check                     false
% 3.11/0.99  --clausify_out                          false
% 3.11/0.99  --sig_cnt_out                           false
% 3.11/0.99  --trig_cnt_out                          false
% 3.11/0.99  --trig_cnt_out_tolerance                1.
% 3.11/0.99  --trig_cnt_out_sk_spl                   false
% 3.11/0.99  --abstr_cl_out                          false
% 3.11/0.99  
% 3.11/0.99  ------ Global Options
% 3.11/0.99  
% 3.11/0.99  --schedule                              default
% 3.11/0.99  --add_important_lit                     false
% 3.11/0.99  --prop_solver_per_cl                    1000
% 3.11/0.99  --min_unsat_core                        false
% 3.11/0.99  --soft_assumptions                      false
% 3.11/0.99  --soft_lemma_size                       3
% 3.11/0.99  --prop_impl_unit_size                   0
% 3.11/0.99  --prop_impl_unit                        []
% 3.11/0.99  --share_sel_clauses                     true
% 3.11/0.99  --reset_solvers                         false
% 3.11/0.99  --bc_imp_inh                            [conj_cone]
% 3.11/0.99  --conj_cone_tolerance                   3.
% 3.11/0.99  --extra_neg_conj                        none
% 3.11/0.99  --large_theory_mode                     true
% 3.11/0.99  --prolific_symb_bound                   200
% 3.11/0.99  --lt_threshold                          2000
% 3.11/0.99  --clause_weak_htbl                      true
% 3.11/0.99  --gc_record_bc_elim                     false
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing Options
% 3.11/0.99  
% 3.11/0.99  --preprocessing_flag                    true
% 3.11/0.99  --time_out_prep_mult                    0.1
% 3.11/0.99  --splitting_mode                        input
% 3.11/0.99  --splitting_grd                         true
% 3.11/0.99  --splitting_cvd                         false
% 3.11/0.99  --splitting_cvd_svl                     false
% 3.11/0.99  --splitting_nvd                         32
% 3.11/0.99  --sub_typing                            true
% 3.11/0.99  --prep_gs_sim                           true
% 3.11/0.99  --prep_unflatten                        true
% 3.11/0.99  --prep_res_sim                          true
% 3.11/0.99  --prep_upred                            true
% 3.11/0.99  --prep_sem_filter                       exhaustive
% 3.11/0.99  --prep_sem_filter_out                   false
% 3.11/0.99  --pred_elim                             true
% 3.11/0.99  --res_sim_input                         true
% 3.11/0.99  --eq_ax_congr_red                       true
% 3.11/0.99  --pure_diseq_elim                       true
% 3.11/0.99  --brand_transform                       false
% 3.11/0.99  --non_eq_to_eq                          false
% 3.11/0.99  --prep_def_merge                        true
% 3.11/0.99  --prep_def_merge_prop_impl              false
% 3.11/0.99  --prep_def_merge_mbd                    true
% 3.11/0.99  --prep_def_merge_tr_red                 false
% 3.11/0.99  --prep_def_merge_tr_cl                  false
% 3.11/0.99  --smt_preprocessing                     true
% 3.11/0.99  --smt_ac_axioms                         fast
% 3.11/0.99  --preprocessed_out                      false
% 3.11/0.99  --preprocessed_stats                    false
% 3.11/0.99  
% 3.11/0.99  ------ Abstraction refinement Options
% 3.11/0.99  
% 3.11/0.99  --abstr_ref                             []
% 3.11/0.99  --abstr_ref_prep                        false
% 3.11/0.99  --abstr_ref_until_sat                   false
% 3.11/0.99  --abstr_ref_sig_restrict                funpre
% 3.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/0.99  --abstr_ref_under                       []
% 3.11/0.99  
% 3.11/0.99  ------ SAT Options
% 3.11/0.99  
% 3.11/0.99  --sat_mode                              false
% 3.11/0.99  --sat_fm_restart_options                ""
% 3.11/0.99  --sat_gr_def                            false
% 3.11/0.99  --sat_epr_types                         true
% 3.11/0.99  --sat_non_cyclic_types                  false
% 3.11/0.99  --sat_finite_models                     false
% 3.11/0.99  --sat_fm_lemmas                         false
% 3.11/0.99  --sat_fm_prep                           false
% 3.11/0.99  --sat_fm_uc_incr                        true
% 3.11/0.99  --sat_out_model                         small
% 3.11/0.99  --sat_out_clauses                       false
% 3.11/0.99  
% 3.11/0.99  ------ QBF Options
% 3.11/0.99  
% 3.11/0.99  --qbf_mode                              false
% 3.11/0.99  --qbf_elim_univ                         false
% 3.11/0.99  --qbf_dom_inst                          none
% 3.11/0.99  --qbf_dom_pre_inst                      false
% 3.11/0.99  --qbf_sk_in                             false
% 3.11/0.99  --qbf_pred_elim                         true
% 3.11/0.99  --qbf_split                             512
% 3.11/0.99  
% 3.11/0.99  ------ BMC1 Options
% 3.11/0.99  
% 3.11/0.99  --bmc1_incremental                      false
% 3.11/0.99  --bmc1_axioms                           reachable_all
% 3.11/0.99  --bmc1_min_bound                        0
% 3.11/0.99  --bmc1_max_bound                        -1
% 3.11/0.99  --bmc1_max_bound_default                -1
% 3.11/0.99  --bmc1_symbol_reachability              true
% 3.11/0.99  --bmc1_property_lemmas                  false
% 3.11/0.99  --bmc1_k_induction                      false
% 3.11/0.99  --bmc1_non_equiv_states                 false
% 3.11/0.99  --bmc1_deadlock                         false
% 3.11/0.99  --bmc1_ucm                              false
% 3.11/0.99  --bmc1_add_unsat_core                   none
% 3.11/0.99  --bmc1_unsat_core_children              false
% 3.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/0.99  --bmc1_out_stat                         full
% 3.11/0.99  --bmc1_ground_init                      false
% 3.11/0.99  --bmc1_pre_inst_next_state              false
% 3.11/0.99  --bmc1_pre_inst_state                   false
% 3.11/0.99  --bmc1_pre_inst_reach_state             false
% 3.11/0.99  --bmc1_out_unsat_core                   false
% 3.11/0.99  --bmc1_aig_witness_out                  false
% 3.11/0.99  --bmc1_verbose                          false
% 3.11/0.99  --bmc1_dump_clauses_tptp                false
% 3.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.11/0.99  --bmc1_dump_file                        -
% 3.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.11/0.99  --bmc1_ucm_extend_mode                  1
% 3.11/0.99  --bmc1_ucm_init_mode                    2
% 3.11/0.99  --bmc1_ucm_cone_mode                    none
% 3.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.11/0.99  --bmc1_ucm_relax_model                  4
% 3.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/0.99  --bmc1_ucm_layered_model                none
% 3.11/0.99  --bmc1_ucm_max_lemma_size               10
% 3.11/0.99  
% 3.11/0.99  ------ AIG Options
% 3.11/0.99  
% 3.11/0.99  --aig_mode                              false
% 3.11/0.99  
% 3.11/0.99  ------ Instantiation Options
% 3.11/0.99  
% 3.11/0.99  --instantiation_flag                    true
% 3.11/0.99  --inst_sos_flag                         false
% 3.11/0.99  --inst_sos_phase                        true
% 3.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel_side                     num_symb
% 3.11/0.99  --inst_solver_per_active                1400
% 3.11/0.99  --inst_solver_calls_frac                1.
% 3.11/0.99  --inst_passive_queue_type               priority_queues
% 3.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/0.99  --inst_passive_queues_freq              [25;2]
% 3.11/0.99  --inst_dismatching                      true
% 3.11/0.99  --inst_eager_unprocessed_to_passive     true
% 3.11/0.99  --inst_prop_sim_given                   true
% 3.11/0.99  --inst_prop_sim_new                     false
% 3.11/0.99  --inst_subs_new                         false
% 3.11/0.99  --inst_eq_res_simp                      false
% 3.11/0.99  --inst_subs_given                       false
% 3.11/0.99  --inst_orphan_elimination               true
% 3.11/0.99  --inst_learning_loop_flag               true
% 3.11/0.99  --inst_learning_start                   3000
% 3.11/0.99  --inst_learning_factor                  2
% 3.11/0.99  --inst_start_prop_sim_after_learn       3
% 3.11/0.99  --inst_sel_renew                        solver
% 3.11/0.99  --inst_lit_activity_flag                true
% 3.11/0.99  --inst_restr_to_given                   false
% 3.11/0.99  --inst_activity_threshold               500
% 3.11/0.99  --inst_out_proof                        true
% 3.11/0.99  
% 3.11/0.99  ------ Resolution Options
% 3.11/0.99  
% 3.11/0.99  --resolution_flag                       true
% 3.11/0.99  --res_lit_sel                           adaptive
% 3.11/0.99  --res_lit_sel_side                      none
% 3.11/0.99  --res_ordering                          kbo
% 3.11/0.99  --res_to_prop_solver                    active
% 3.11/0.99  --res_prop_simpl_new                    false
% 3.11/0.99  --res_prop_simpl_given                  true
% 3.11/0.99  --res_passive_queue_type                priority_queues
% 3.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/0.99  --res_passive_queues_freq               [15;5]
% 3.11/0.99  --res_forward_subs                      full
% 3.11/0.99  --res_backward_subs                     full
% 3.11/0.99  --res_forward_subs_resolution           true
% 3.11/0.99  --res_backward_subs_resolution          true
% 3.11/0.99  --res_orphan_elimination                true
% 3.11/0.99  --res_time_limit                        2.
% 3.11/0.99  --res_out_proof                         true
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Options
% 3.11/0.99  
% 3.11/0.99  --superposition_flag                    true
% 3.11/0.99  --sup_passive_queue_type                priority_queues
% 3.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.11/0.99  --demod_completeness_check              fast
% 3.11/0.99  --demod_use_ground                      true
% 3.11/0.99  --sup_to_prop_solver                    passive
% 3.11/0.99  --sup_prop_simpl_new                    true
% 3.11/0.99  --sup_prop_simpl_given                  true
% 3.11/0.99  --sup_fun_splitting                     false
% 3.11/0.99  --sup_smt_interval                      50000
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Simplification Setup
% 3.11/0.99  
% 3.11/0.99  --sup_indices_passive                   []
% 3.11/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_full_bw                           [BwDemod]
% 3.11/0.99  --sup_immed_triv                        [TrivRules]
% 3.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_immed_bw_main                     []
% 3.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  
% 3.11/0.99  ------ Combination Options
% 3.11/0.99  
% 3.11/0.99  --comb_res_mult                         3
% 3.11/0.99  --comb_sup_mult                         2
% 3.11/0.99  --comb_inst_mult                        10
% 3.11/0.99  
% 3.11/0.99  ------ Debug Options
% 3.11/0.99  
% 3.11/0.99  --dbg_backtrace                         false
% 3.11/0.99  --dbg_dump_prop_clauses                 false
% 3.11/0.99  --dbg_dump_prop_clauses_file            -
% 3.11/0.99  --dbg_out_stat                          false
% 3.11/0.99  ------ Parsing...
% 3.11/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.11/0.99  ------ Proving...
% 3.11/0.99  ------ Problem Properties 
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  clauses                                 33
% 3.11/0.99  conjectures                             20
% 3.11/0.99  EPR                                     17
% 3.11/0.99  Horn                                    28
% 3.11/0.99  unary                                   18
% 3.11/0.99  binary                                  5
% 3.11/0.99  lits                                    109
% 3.11/0.99  lits eq                                 11
% 3.11/0.99  fd_pure                                 0
% 3.11/0.99  fd_pseudo                               0
% 3.11/0.99  fd_cond                                 0
% 3.11/0.99  fd_pseudo_cond                          0
% 3.11/0.99  AC symbols                              0
% 3.11/0.99  
% 3.11/0.99  ------ Schedule dynamic 5 is on 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  ------ 
% 3.11/0.99  Current options:
% 3.11/0.99  ------ 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options
% 3.11/0.99  
% 3.11/0.99  --out_options                           all
% 3.11/0.99  --tptp_safe_out                         true
% 3.11/0.99  --problem_path                          ""
% 3.11/0.99  --include_path                          ""
% 3.11/0.99  --clausifier                            res/vclausify_rel
% 3.11/0.99  --clausifier_options                    --mode clausify
% 3.11/0.99  --stdin                                 false
% 3.11/0.99  --stats_out                             all
% 3.11/0.99  
% 3.11/0.99  ------ General Options
% 3.11/0.99  
% 3.11/0.99  --fof                                   false
% 3.11/0.99  --time_out_real                         305.
% 3.11/0.99  --time_out_virtual                      -1.
% 3.11/0.99  --symbol_type_check                     false
% 3.11/0.99  --clausify_out                          false
% 3.11/0.99  --sig_cnt_out                           false
% 3.11/0.99  --trig_cnt_out                          false
% 3.11/0.99  --trig_cnt_out_tolerance                1.
% 3.11/0.99  --trig_cnt_out_sk_spl                   false
% 3.11/0.99  --abstr_cl_out                          false
% 3.11/0.99  
% 3.11/0.99  ------ Global Options
% 3.11/0.99  
% 3.11/0.99  --schedule                              default
% 3.11/0.99  --add_important_lit                     false
% 3.11/0.99  --prop_solver_per_cl                    1000
% 3.11/0.99  --min_unsat_core                        false
% 3.11/0.99  --soft_assumptions                      false
% 3.11/0.99  --soft_lemma_size                       3
% 3.11/0.99  --prop_impl_unit_size                   0
% 3.11/0.99  --prop_impl_unit                        []
% 3.11/0.99  --share_sel_clauses                     true
% 3.11/0.99  --reset_solvers                         false
% 3.11/0.99  --bc_imp_inh                            [conj_cone]
% 3.11/0.99  --conj_cone_tolerance                   3.
% 3.11/0.99  --extra_neg_conj                        none
% 3.11/0.99  --large_theory_mode                     true
% 3.11/0.99  --prolific_symb_bound                   200
% 3.11/0.99  --lt_threshold                          2000
% 3.11/0.99  --clause_weak_htbl                      true
% 3.11/0.99  --gc_record_bc_elim                     false
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing Options
% 3.11/0.99  
% 3.11/0.99  --preprocessing_flag                    true
% 3.11/0.99  --time_out_prep_mult                    0.1
% 3.11/0.99  --splitting_mode                        input
% 3.11/0.99  --splitting_grd                         true
% 3.11/0.99  --splitting_cvd                         false
% 3.11/0.99  --splitting_cvd_svl                     false
% 3.11/0.99  --splitting_nvd                         32
% 3.11/0.99  --sub_typing                            true
% 3.11/0.99  --prep_gs_sim                           true
% 3.11/0.99  --prep_unflatten                        true
% 3.11/0.99  --prep_res_sim                          true
% 3.11/0.99  --prep_upred                            true
% 3.11/0.99  --prep_sem_filter                       exhaustive
% 3.11/0.99  --prep_sem_filter_out                   false
% 3.11/0.99  --pred_elim                             true
% 3.11/0.99  --res_sim_input                         true
% 3.11/0.99  --eq_ax_congr_red                       true
% 3.11/0.99  --pure_diseq_elim                       true
% 3.11/0.99  --brand_transform                       false
% 3.11/0.99  --non_eq_to_eq                          false
% 3.11/0.99  --prep_def_merge                        true
% 3.11/0.99  --prep_def_merge_prop_impl              false
% 3.11/0.99  --prep_def_merge_mbd                    true
% 3.11/0.99  --prep_def_merge_tr_red                 false
% 3.11/0.99  --prep_def_merge_tr_cl                  false
% 3.11/0.99  --smt_preprocessing                     true
% 3.11/0.99  --smt_ac_axioms                         fast
% 3.11/0.99  --preprocessed_out                      false
% 3.11/0.99  --preprocessed_stats                    false
% 3.11/0.99  
% 3.11/0.99  ------ Abstraction refinement Options
% 3.11/0.99  
% 3.11/0.99  --abstr_ref                             []
% 3.11/0.99  --abstr_ref_prep                        false
% 3.11/0.99  --abstr_ref_until_sat                   false
% 3.11/0.99  --abstr_ref_sig_restrict                funpre
% 3.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/0.99  --abstr_ref_under                       []
% 3.11/0.99  
% 3.11/0.99  ------ SAT Options
% 3.11/0.99  
% 3.11/0.99  --sat_mode                              false
% 3.11/0.99  --sat_fm_restart_options                ""
% 3.11/0.99  --sat_gr_def                            false
% 3.11/0.99  --sat_epr_types                         true
% 3.11/0.99  --sat_non_cyclic_types                  false
% 3.11/0.99  --sat_finite_models                     false
% 3.11/0.99  --sat_fm_lemmas                         false
% 3.11/0.99  --sat_fm_prep                           false
% 3.11/0.99  --sat_fm_uc_incr                        true
% 3.11/0.99  --sat_out_model                         small
% 3.11/0.99  --sat_out_clauses                       false
% 3.11/0.99  
% 3.11/0.99  ------ QBF Options
% 3.11/0.99  
% 3.11/0.99  --qbf_mode                              false
% 3.11/0.99  --qbf_elim_univ                         false
% 3.11/0.99  --qbf_dom_inst                          none
% 3.11/0.99  --qbf_dom_pre_inst                      false
% 3.11/0.99  --qbf_sk_in                             false
% 3.11/0.99  --qbf_pred_elim                         true
% 3.11/0.99  --qbf_split                             512
% 3.11/0.99  
% 3.11/0.99  ------ BMC1 Options
% 3.11/0.99  
% 3.11/0.99  --bmc1_incremental                      false
% 3.11/0.99  --bmc1_axioms                           reachable_all
% 3.11/0.99  --bmc1_min_bound                        0
% 3.11/0.99  --bmc1_max_bound                        -1
% 3.11/0.99  --bmc1_max_bound_default                -1
% 3.11/0.99  --bmc1_symbol_reachability              true
% 3.11/0.99  --bmc1_property_lemmas                  false
% 3.11/0.99  --bmc1_k_induction                      false
% 3.11/0.99  --bmc1_non_equiv_states                 false
% 3.11/0.99  --bmc1_deadlock                         false
% 3.11/0.99  --bmc1_ucm                              false
% 3.11/0.99  --bmc1_add_unsat_core                   none
% 3.11/0.99  --bmc1_unsat_core_children              false
% 3.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/0.99  --bmc1_out_stat                         full
% 3.11/0.99  --bmc1_ground_init                      false
% 3.11/0.99  --bmc1_pre_inst_next_state              false
% 3.11/0.99  --bmc1_pre_inst_state                   false
% 3.11/0.99  --bmc1_pre_inst_reach_state             false
% 3.11/0.99  --bmc1_out_unsat_core                   false
% 3.11/0.99  --bmc1_aig_witness_out                  false
% 3.11/0.99  --bmc1_verbose                          false
% 3.11/0.99  --bmc1_dump_clauses_tptp                false
% 3.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.11/0.99  --bmc1_dump_file                        -
% 3.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.11/0.99  --bmc1_ucm_extend_mode                  1
% 3.11/0.99  --bmc1_ucm_init_mode                    2
% 3.11/0.99  --bmc1_ucm_cone_mode                    none
% 3.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.11/0.99  --bmc1_ucm_relax_model                  4
% 3.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/0.99  --bmc1_ucm_layered_model                none
% 3.11/0.99  --bmc1_ucm_max_lemma_size               10
% 3.11/0.99  
% 3.11/0.99  ------ AIG Options
% 3.11/0.99  
% 3.11/0.99  --aig_mode                              false
% 3.11/0.99  
% 3.11/0.99  ------ Instantiation Options
% 3.11/0.99  
% 3.11/0.99  --instantiation_flag                    true
% 3.11/0.99  --inst_sos_flag                         false
% 3.11/0.99  --inst_sos_phase                        true
% 3.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel_side                     none
% 3.11/0.99  --inst_solver_per_active                1400
% 3.11/0.99  --inst_solver_calls_frac                1.
% 3.11/0.99  --inst_passive_queue_type               priority_queues
% 3.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/0.99  --inst_passive_queues_freq              [25;2]
% 3.11/0.99  --inst_dismatching                      true
% 3.11/0.99  --inst_eager_unprocessed_to_passive     true
% 3.11/0.99  --inst_prop_sim_given                   true
% 3.11/0.99  --inst_prop_sim_new                     false
% 3.11/0.99  --inst_subs_new                         false
% 3.11/0.99  --inst_eq_res_simp                      false
% 3.11/0.99  --inst_subs_given                       false
% 3.11/0.99  --inst_orphan_elimination               true
% 3.11/0.99  --inst_learning_loop_flag               true
% 3.11/0.99  --inst_learning_start                   3000
% 3.11/0.99  --inst_learning_factor                  2
% 3.11/0.99  --inst_start_prop_sim_after_learn       3
% 3.11/0.99  --inst_sel_renew                        solver
% 3.11/0.99  --inst_lit_activity_flag                true
% 3.11/0.99  --inst_restr_to_given                   false
% 3.11/0.99  --inst_activity_threshold               500
% 3.11/0.99  --inst_out_proof                        true
% 3.11/0.99  
% 3.11/0.99  ------ Resolution Options
% 3.11/0.99  
% 3.11/0.99  --resolution_flag                       false
% 3.11/0.99  --res_lit_sel                           adaptive
% 3.11/0.99  --res_lit_sel_side                      none
% 3.11/0.99  --res_ordering                          kbo
% 3.11/0.99  --res_to_prop_solver                    active
% 3.11/0.99  --res_prop_simpl_new                    false
% 3.11/0.99  --res_prop_simpl_given                  true
% 3.11/0.99  --res_passive_queue_type                priority_queues
% 3.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/0.99  --res_passive_queues_freq               [15;5]
% 3.11/0.99  --res_forward_subs                      full
% 3.11/0.99  --res_backward_subs                     full
% 3.11/0.99  --res_forward_subs_resolution           true
% 3.11/0.99  --res_backward_subs_resolution          true
% 3.11/0.99  --res_orphan_elimination                true
% 3.11/0.99  --res_time_limit                        2.
% 3.11/0.99  --res_out_proof                         true
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Options
% 3.11/0.99  
% 3.11/0.99  --superposition_flag                    true
% 3.11/0.99  --sup_passive_queue_type                priority_queues
% 3.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.11/0.99  --demod_completeness_check              fast
% 3.11/0.99  --demod_use_ground                      true
% 3.11/0.99  --sup_to_prop_solver                    passive
% 3.11/0.99  --sup_prop_simpl_new                    true
% 3.11/0.99  --sup_prop_simpl_given                  true
% 3.11/0.99  --sup_fun_splitting                     false
% 3.11/0.99  --sup_smt_interval                      50000
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Simplification Setup
% 3.11/0.99  
% 3.11/0.99  --sup_indices_passive                   []
% 3.11/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_full_bw                           [BwDemod]
% 3.11/0.99  --sup_immed_triv                        [TrivRules]
% 3.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_immed_bw_main                     []
% 3.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  
% 3.11/0.99  ------ Combination Options
% 3.11/0.99  
% 3.11/0.99  --comb_res_mult                         3
% 3.11/0.99  --comb_sup_mult                         2
% 3.11/0.99  --comb_inst_mult                        10
% 3.11/0.99  
% 3.11/0.99  ------ Debug Options
% 3.11/0.99  
% 3.11/0.99  --dbg_backtrace                         false
% 3.11/0.99  --dbg_dump_prop_clauses                 false
% 3.11/0.99  --dbg_dump_prop_clauses_file            -
% 3.11/0.99  --dbg_out_stat                          false
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  ------ Proving...
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  % SZS status Theorem for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  fof(f10,axiom,(
% 3.11/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f28,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f10])).
% 3.11/0.99  
% 3.11/0.99  fof(f29,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.11/0.99    inference(flattening,[],[f28])).
% 3.11/0.99  
% 3.11/0.99  fof(f35,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.11/0.99    inference(nnf_transformation,[],[f29])).
% 3.11/0.99  
% 3.11/0.99  fof(f58,plain,(
% 3.11/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f35])).
% 3.11/0.99  
% 3.11/0.99  fof(f84,plain,(
% 3.11/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.11/0.99    inference(equality_resolution,[],[f58])).
% 3.11/0.99  
% 3.11/0.99  fof(f12,conjecture,(
% 3.11/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f13,negated_conjecture,(
% 3.11/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 3.11/0.99    inference(negated_conjecture,[],[f12])).
% 3.11/0.99  
% 3.11/0.99  fof(f32,plain,(
% 3.11/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f13])).
% 3.11/0.99  
% 3.11/0.99  fof(f33,plain,(
% 3.11/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.11/0.99    inference(flattening,[],[f32])).
% 3.11/0.99  
% 3.11/0.99  fof(f36,plain,(
% 3.11/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.11/0.99    inference(nnf_transformation,[],[f33])).
% 3.11/0.99  
% 3.11/0.99  fof(f37,plain,(
% 3.11/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.11/0.99    inference(flattening,[],[f36])).
% 3.11/0.99  
% 3.11/0.99  fof(f45,plain,(
% 3.11/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | r1_tmap_1(X3,X0,X4,X6)) & sK7 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 3.11/0.99    introduced(choice_axiom,[])).
% 3.11/0.99  
% 3.11/0.99  fof(f44,plain,(
% 3.11/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,sK6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,sK6)) & sK6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 3.11/0.99    introduced(choice_axiom,[])).
% 3.11/0.99  
% 3.11/0.99  fof(f43,plain,(
% 3.11/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(X2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 3.11/0.99    introduced(choice_axiom,[])).
% 3.11/0.99  
% 3.11/0.99  fof(f42,plain,(
% 3.11/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7) | ~r1_tmap_1(X3,X0,sK4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7) | r1_tmap_1(X3,X0,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 3.11/0.99    introduced(choice_axiom,[])).
% 3.11/0.99  
% 3.11/0.99  fof(f41,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7) | ~r1_tmap_1(sK3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7) | r1_tmap_1(sK3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 3.11/0.99    introduced(choice_axiom,[])).
% 3.11/0.99  
% 3.11/0.99  fof(f40,plain,(
% 3.11/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 3.11/0.99    introduced(choice_axiom,[])).
% 3.11/0.99  
% 3.11/0.99  fof(f39,plain,(
% 3.11/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.11/0.99    introduced(choice_axiom,[])).
% 3.11/0.99  
% 3.11/0.99  fof(f38,plain,(
% 3.11/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.11/0.99    introduced(choice_axiom,[])).
% 3.11/0.99  
% 3.11/0.99  fof(f46,plain,(
% 3.11/0.99    ((((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.11/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f37,f45,f44,f43,f42,f41,f40,f39,f38])).
% 3.11/0.99  
% 3.11/0.99  fof(f78,plain,(
% 3.11/0.99    r2_hidden(sK6,sK5)),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f3,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f16,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.11/0.99    inference(ennf_transformation,[],[f3])).
% 3.11/0.99  
% 3.11/0.99  fof(f17,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.11/0.99    inference(flattening,[],[f16])).
% 3.11/0.99  
% 3.11/0.99  fof(f50,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f17])).
% 3.11/0.99  
% 3.11/0.99  fof(f71,plain,(
% 3.11/0.99    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f70,plain,(
% 3.11/0.99    v1_funct_1(sK4)),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f57,plain,(
% 3.11/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f35])).
% 3.11/0.99  
% 3.11/0.99  fof(f85,plain,(
% 3.11/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.11/0.99    inference(equality_resolution,[],[f57])).
% 3.11/0.99  
% 3.11/0.99  fof(f7,axiom,(
% 3.11/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f23,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f7])).
% 3.11/0.99  
% 3.11/0.99  fof(f24,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.11/0.99    inference(flattening,[],[f23])).
% 3.11/0.99  
% 3.11/0.99  fof(f54,plain,(
% 3.11/0.99    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f24])).
% 3.11/0.99  
% 3.11/0.99  fof(f2,axiom,(
% 3.11/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f34,plain,(
% 3.11/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.11/0.99    inference(nnf_transformation,[],[f2])).
% 3.11/0.99  
% 3.11/0.99  fof(f49,plain,(
% 3.11/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f34])).
% 3.11/0.99  
% 3.11/0.99  fof(f1,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f14,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.11/0.99    inference(ennf_transformation,[],[f1])).
% 3.11/0.99  
% 3.11/0.99  fof(f15,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.11/0.99    inference(flattening,[],[f14])).
% 3.11/0.99  
% 3.11/0.99  fof(f47,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f15])).
% 3.11/0.99  
% 3.11/0.99  fof(f4,axiom,(
% 3.11/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f18,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f4])).
% 3.11/0.99  
% 3.11/0.99  fof(f19,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.11/0.99    inference(flattening,[],[f18])).
% 3.11/0.99  
% 3.11/0.99  fof(f51,plain,(
% 3.11/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f19])).
% 3.11/0.99  
% 3.11/0.99  fof(f8,axiom,(
% 3.11/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f25,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f8])).
% 3.11/0.99  
% 3.11/0.99  fof(f26,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.11/0.99    inference(flattening,[],[f25])).
% 3.11/0.99  
% 3.11/0.99  fof(f55,plain,(
% 3.11/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f26])).
% 3.11/0.99  
% 3.11/0.99  fof(f11,axiom,(
% 3.11/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f30,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f11])).
% 3.11/0.99  
% 3.11/0.99  fof(f31,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.11/0.99    inference(flattening,[],[f30])).
% 3.11/0.99  
% 3.11/0.99  fof(f59,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f31])).
% 3.11/0.99  
% 3.11/0.99  fof(f5,axiom,(
% 3.11/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f20,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.11/0.99    inference(ennf_transformation,[],[f5])).
% 3.11/0.99  
% 3.11/0.99  fof(f52,plain,(
% 3.11/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f20])).
% 3.11/0.99  
% 3.11/0.99  fof(f6,axiom,(
% 3.11/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f21,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.11/0.99    inference(ennf_transformation,[],[f6])).
% 3.11/0.99  
% 3.11/0.99  fof(f22,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.11/0.99    inference(flattening,[],[f21])).
% 3.11/0.99  
% 3.11/0.99  fof(f53,plain,(
% 3.11/0.99    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f22])).
% 3.11/0.99  
% 3.11/0.99  fof(f83,plain,(
% 3.11/0.99    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.11/0.99    inference(equality_resolution,[],[f53])).
% 3.11/0.99  
% 3.11/0.99  fof(f48,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f34])).
% 3.11/0.99  
% 3.11/0.99  fof(f9,axiom,(
% 3.11/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f27,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.11/0.99    inference(ennf_transformation,[],[f9])).
% 3.11/0.99  
% 3.11/0.99  fof(f56,plain,(
% 3.11/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f27])).
% 3.11/0.99  
% 3.11/0.99  fof(f80,plain,(
% 3.11/0.99    sK6 = sK7),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f82,plain,(
% 3.11/0.99    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f81,plain,(
% 3.11/0.99    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f79,plain,(
% 3.11/0.99    r1_tarski(sK5,u1_struct_0(sK2))),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f77,plain,(
% 3.11/0.99    v3_pre_topc(sK5,sK1)),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f74,plain,(
% 3.11/0.99    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f73,plain,(
% 3.11/0.99    m1_pre_topc(sK2,sK3)),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f72,plain,(
% 3.11/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f69,plain,(
% 3.11/0.99    m1_pre_topc(sK3,sK1)),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f68,plain,(
% 3.11/0.99    ~v2_struct_0(sK3)),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f66,plain,(
% 3.11/0.99    ~v2_struct_0(sK2)),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f65,plain,(
% 3.11/0.99    l1_pre_topc(sK1)),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f64,plain,(
% 3.11/0.99    v2_pre_topc(sK1)),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f63,plain,(
% 3.11/0.99    ~v2_struct_0(sK1)),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f62,plain,(
% 3.11/0.99    l1_pre_topc(sK0)),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f61,plain,(
% 3.11/0.99    v2_pre_topc(sK0)),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f60,plain,(
% 3.11/0.99    ~v2_struct_0(sK0)),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1150,plain,
% 3.11/0.99      ( ~ r1_tmap_1(X0_53,X1_53,X0_54,X1_54)
% 3.11/0.99      | r1_tmap_1(X0_53,X1_53,X2_54,X3_54)
% 3.11/0.99      | X2_54 != X0_54
% 3.11/0.99      | X3_54 != X1_54 ),
% 3.11/0.99      theory(equality) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2711,plain,
% 3.11/0.99      ( r1_tmap_1(sK2,sK0,X0_54,X1_54)
% 3.11/0.99      | ~ r1_tmap_1(sK2,sK0,X2_54,sK6)
% 3.11/0.99      | X0_54 != X2_54
% 3.11/0.99      | X1_54 != sK6 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1150]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3114,plain,
% 3.11/0.99      ( ~ r1_tmap_1(sK2,sK0,X0_54,sK6)
% 3.11/0.99      | r1_tmap_1(sK2,sK0,X1_54,sK7)
% 3.11/0.99      | X1_54 != X0_54
% 3.11/0.99      | sK7 != sK6 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_2711]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_6289,plain,
% 3.11/0.99      ( r1_tmap_1(sK2,sK0,X0_54,sK7)
% 3.11/0.99      | ~ r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
% 3.11/0.99      | X0_54 != k2_tmap_1(sK3,sK0,sK4,sK2)
% 3.11/0.99      | sK7 != sK6 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_3114]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_6873,plain,
% 3.11/0.99      ( r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK7)
% 3.11/0.99      | ~ r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
% 3.11/0.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) != k2_tmap_1(sK3,sK0,sK4,sK2)
% 3.11/0.99      | sK7 != sK6 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_6289]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_6874,plain,
% 3.11/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) != k2_tmap_1(sK3,sK0,sK4,sK2)
% 3.11/0.99      | sK7 != sK6
% 3.11/0.99      | r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK7) = iProver_top
% 3.11/0.99      | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_6873]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2341,plain,
% 3.11/0.99      ( r1_tmap_1(sK2,sK0,X0_54,X1_54)
% 3.11/0.99      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 3.11/0.99      | X0_54 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 3.11/0.99      | X1_54 != sK7 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1150]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2531,plain,
% 3.11/0.99      ( r1_tmap_1(sK2,sK0,X0_54,sK6)
% 3.11/0.99      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 3.11/0.99      | X0_54 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 3.11/0.99      | sK6 != sK7 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_2341]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_6429,plain,
% 3.11/0.99      ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 3.11/0.99      | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
% 3.11/0.99      | k2_tmap_1(sK3,sK0,sK4,sK2) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 3.11/0.99      | sK6 != sK7 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_2531]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_6433,plain,
% 3.11/0.99      ( k2_tmap_1(sK3,sK0,sK4,sK2) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 3.11/0.99      | sK6 != sK7
% 3.11/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top
% 3.11/0.99      | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_6429]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1141,plain,
% 3.11/0.99      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 3.11/0.99      theory(equality) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3050,plain,
% 3.11/0.99      ( X0_54 != X1_54
% 3.11/0.99      | X0_54 = k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 3.11/0.99      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != X1_54 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1141]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4376,plain,
% 3.11/0.99      ( X0_54 = k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 3.11/0.99      | X0_54 != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
% 3.11/0.99      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_3050]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_6065,plain,
% 3.11/0.99      ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
% 3.11/0.99      | k2_tmap_1(sK3,sK0,sK4,sK2) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 3.11/0.99      | k2_tmap_1(sK3,sK0,sK4,sK2) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_4376]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1140,plain,( X0_54 = X0_54 ),theory(equality) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5627,plain,
% 3.11/0.99      ( k2_tmap_1(sK3,sK0,sK4,sK2) = k2_tmap_1(sK3,sK0,sK4,sK2) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1140]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4753,plain,
% 3.11/0.99      ( X0_54 != X1_54
% 3.11/0.99      | X0_54 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
% 3.11/0.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) != X1_54 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1141]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5392,plain,
% 3.11/0.99      ( X0_54 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
% 3.11/0.99      | X0_54 != k2_tmap_1(sK3,sK0,sK4,sK2)
% 3.11/0.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) != k2_tmap_1(sK3,sK0,sK4,sK2) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_4753]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5626,plain,
% 3.11/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) != k2_tmap_1(sK3,sK0,sK4,sK2)
% 3.11/0.99      | k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
% 3.11/0.99      | k2_tmap_1(sK3,sK0,sK4,sK2) != k2_tmap_1(sK3,sK0,sK4,sK2) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_5392]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4367,plain,
% 3.11/0.99      ( r1_tmap_1(sK2,sK0,X0_54,X1_54)
% 3.11/0.99      | ~ r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK7)
% 3.11/0.99      | X0_54 != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
% 3.11/0.99      | X1_54 != sK7 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1150]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4974,plain,
% 3.11/0.99      ( r1_tmap_1(sK2,sK0,X0_54,sK7)
% 3.11/0.99      | ~ r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK7)
% 3.11/0.99      | X0_54 != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
% 3.11/0.99      | sK7 != sK7 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_4367]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5276,plain,
% 3.11/0.99      ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 3.11/0.99      | ~ r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK7)
% 3.11/0.99      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
% 3.11/0.99      | sK7 != sK7 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_4974]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5277,plain,
% 3.11/0.99      ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
% 3.11/0.99      | sK7 != sK7
% 3.11/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top
% 3.11/0.99      | r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK7) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_5276]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_10,plain,
% 3.11/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.11/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.11/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.11/0.99      | ~ v3_pre_topc(X5,X0)
% 3.11/0.99      | ~ m1_pre_topc(X4,X0)
% 3.11/0.99      | ~ r2_hidden(X3,X5)
% 3.11/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.11/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.11/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.11/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.11/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | v2_struct_0(X0)
% 3.11/0.99      | v2_struct_0(X4)
% 3.11/0.99      | ~ v1_funct_1(X2)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ l1_pre_topc(X0)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_17,negated_conjecture,
% 3.11/0.99      ( r2_hidden(sK6,sK5) ),
% 3.11/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_519,plain,
% 3.11/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.11/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.11/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.11/0.99      | ~ v3_pre_topc(X5,X0)
% 3.11/0.99      | ~ m1_pre_topc(X4,X0)
% 3.11/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.11/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.11/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.11/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.11/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.11/0.99      | v2_struct_0(X0)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | v2_struct_0(X4)
% 3.11/0.99      | ~ v1_funct_1(X2)
% 3.11/0.99      | ~ l1_pre_topc(X0)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X0)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | sK5 != X5
% 3.11/0.99      | sK6 != X3 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_520,plain,
% 3.11/0.99      ( r1_tmap_1(X0,X1,X2,sK6)
% 3.11/0.99      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
% 3.11/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.11/0.99      | ~ v3_pre_topc(sK5,X0)
% 3.11/0.99      | ~ m1_pre_topc(X3,X0)
% 3.11/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 3.11/0.99      | v2_struct_0(X0)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | v2_struct_0(X3)
% 3.11/0.99      | ~ v1_funct_1(X2)
% 3.11/0.99      | ~ l1_pre_topc(X0)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X0)
% 3.11/0.99      | ~ v2_pre_topc(X1) ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_519]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3,plain,
% 3.11/0.99      ( ~ r2_hidden(X0,X1)
% 3.11/0.99      | m1_subset_1(X0,X2)
% 3.11/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.11/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_448,plain,
% 3.11/0.99      ( m1_subset_1(X0,X1)
% 3.11/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.11/0.99      | sK5 != X2
% 3.11/0.99      | sK6 != X0 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_17]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_449,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0)) | m1_subset_1(sK6,X0) ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_448]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_542,plain,
% 3.11/0.99      ( r1_tmap_1(X0,X1,X2,sK6)
% 3.11/0.99      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
% 3.11/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.11/0.99      | ~ v3_pre_topc(sK5,X0)
% 3.11/0.99      | ~ m1_pre_topc(X3,X0)
% 3.11/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 3.11/0.99      | v2_struct_0(X0)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | v2_struct_0(X3)
% 3.11/0.99      | ~ v1_funct_1(X2)
% 3.11/0.99      | ~ l1_pre_topc(X0)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X0)
% 3.11/0.99      | ~ v2_pre_topc(X1) ),
% 3.11/0.99      inference(forward_subsumption_resolution,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_520,c_449]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_24,negated_conjecture,
% 3.11/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
% 3.11/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_679,plain,
% 3.11/0.99      ( r1_tmap_1(X0,X1,X2,sK6)
% 3.11/0.99      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
% 3.11/0.99      | ~ v3_pre_topc(sK5,X0)
% 3.11/0.99      | ~ m1_pre_topc(X3,X0)
% 3.11/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 3.11/0.99      | v2_struct_0(X0)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | v2_struct_0(X3)
% 3.11/0.99      | ~ v1_funct_1(X2)
% 3.11/0.99      | ~ l1_pre_topc(X0)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X0)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 3.11/0.99      | sK4 != X2 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_542,c_24]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_680,plain,
% 3.11/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 3.11/0.99      | r1_tmap_1(X2,X1,sK4,sK6)
% 3.11/0.99      | ~ v3_pre_topc(sK5,X2)
% 3.11/0.99      | ~ m1_pre_topc(X0,X2)
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 3.11/0.99      | v2_struct_0(X2)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | v2_struct_0(X0)
% 3.11/0.99      | ~ v1_funct_1(sK4)
% 3.11/0.99      | ~ l1_pre_topc(X2)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X2)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_679]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_25,negated_conjecture,
% 3.11/0.99      ( v1_funct_1(sK4) ),
% 3.11/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_684,plain,
% 3.11/0.99      ( v2_struct_0(X0)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | v2_struct_0(X2)
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
% 3.11/0.99      | ~ m1_pre_topc(X0,X2)
% 3.11/0.99      | ~ v3_pre_topc(sK5,X2)
% 3.11/0.99      | r1_tmap_1(X2,X1,sK4,sK6)
% 3.11/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 3.11/0.99      | ~ l1_pre_topc(X2)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X2)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_680,c_25]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_685,plain,
% 3.11/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 3.11/0.99      | r1_tmap_1(X2,X1,sK4,sK6)
% 3.11/0.99      | ~ v3_pre_topc(sK5,X2)
% 3.11/0.99      | ~ m1_pre_topc(X0,X2)
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 3.11/0.99      | v2_struct_0(X0)
% 3.11/0.99      | v2_struct_0(X2)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ l1_pre_topc(X2)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X2)
% 3.11/0.99      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(renaming,[status(thm)],[c_684]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1107,plain,
% 3.11/0.99      ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,sK4,X0_53),sK6)
% 3.11/0.99      | r1_tmap_1(X2_53,X1_53,sK4,sK6)
% 3.11/0.99      | ~ v3_pre_topc(sK5,X2_53)
% 3.11/0.99      | ~ m1_pre_topc(X0_53,X2_53)
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2_53)))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0_53))
% 3.11/0.99      | v2_struct_0(X0_53)
% 3.11/0.99      | v2_struct_0(X2_53)
% 3.11/0.99      | v2_struct_0(X1_53)
% 3.11/0.99      | ~ l1_pre_topc(X1_53)
% 3.11/0.99      | ~ l1_pre_topc(X2_53)
% 3.11/0.99      | ~ v2_pre_topc(X1_53)
% 3.11/0.99      | ~ v2_pre_topc(X2_53)
% 3.11/0.99      | u1_struct_0(X2_53) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(subtyping,[status(esa)],[c_685]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2661,plain,
% 3.11/0.99      ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK3,X1_53,sK4,X0_53),sK6)
% 3.11/0.99      | r1_tmap_1(sK3,X1_53,sK4,sK6)
% 3.11/0.99      | ~ v3_pre_topc(sK5,sK3)
% 3.11/0.99      | ~ m1_pre_topc(X0_53,sK3)
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0_53))
% 3.11/0.99      | v2_struct_0(X0_53)
% 3.11/0.99      | v2_struct_0(X1_53)
% 3.11/0.99      | v2_struct_0(sK3)
% 3.11/0.99      | ~ l1_pre_topc(X1_53)
% 3.11/0.99      | ~ l1_pre_topc(sK3)
% 3.11/0.99      | ~ v2_pre_topc(X1_53)
% 3.11/0.99      | ~ v2_pre_topc(sK3)
% 3.11/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK0)
% 3.11/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1107]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4357,plain,
% 3.11/0.99      ( r1_tmap_1(sK3,X0_53,sK4,sK6)
% 3.11/0.99      | ~ r1_tmap_1(sK2,X0_53,k2_tmap_1(sK3,X0_53,sK4,sK2),sK6)
% 3.11/0.99      | ~ v3_pre_topc(sK5,sK3)
% 3.11/0.99      | ~ m1_pre_topc(sK2,sK3)
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 3.11/0.99      | v2_struct_0(X0_53)
% 3.11/0.99      | v2_struct_0(sK3)
% 3.11/0.99      | v2_struct_0(sK2)
% 3.11/0.99      | ~ l1_pre_topc(X0_53)
% 3.11/0.99      | ~ l1_pre_topc(sK3)
% 3.11/0.99      | ~ v2_pre_topc(X0_53)
% 3.11/0.99      | ~ v2_pre_topc(sK3)
% 3.11/0.99      | u1_struct_0(X0_53) != u1_struct_0(sK0)
% 3.11/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_2661]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4358,plain,
% 3.11/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK0)
% 3.11/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.11/0.99      | r1_tmap_1(sK3,X0_53,sK4,sK6) = iProver_top
% 3.11/0.99      | r1_tmap_1(sK2,X0_53,k2_tmap_1(sK3,X0_53,sK4,sK2),sK6) != iProver_top
% 3.11/0.99      | v3_pre_topc(sK5,sK3) != iProver_top
% 3.11/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.11/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.11/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 3.11/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53)))) != iProver_top
% 3.11/0.99      | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
% 3.11/0.99      | v2_struct_0(X0_53) = iProver_top
% 3.11/0.99      | v2_struct_0(sK3) = iProver_top
% 3.11/0.99      | v2_struct_0(sK2) = iProver_top
% 3.11/0.99      | l1_pre_topc(X0_53) != iProver_top
% 3.11/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.11/0.99      | v2_pre_topc(X0_53) != iProver_top
% 3.11/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_4357]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4360,plain,
% 3.11/0.99      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 3.11/0.99      | r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 3.11/0.99      | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) != iProver_top
% 3.11/0.99      | v3_pre_topc(sK5,sK3) != iProver_top
% 3.11/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.11/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.11/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 3.11/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 3.11/0.99      | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
% 3.11/0.99      | v2_struct_0(sK3) = iProver_top
% 3.11/0.99      | v2_struct_0(sK0) = iProver_top
% 3.11/0.99      | v2_struct_0(sK2) = iProver_top
% 3.11/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.11/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.11/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.11/0.99      | v2_pre_topc(sK0) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_4358]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3362,plain,
% 3.11/0.99      ( X0_54 != X1_54
% 3.11/0.99      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != X1_54
% 3.11/0.99      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = X0_54 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1141]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3677,plain,
% 3.11/0.99      ( X0_54 != k3_tmap_1(sK1,sK0,sK3,sK2,X1_54)
% 3.11/0.99      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = X0_54
% 3.11/0.99      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,X1_54) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_3362]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4018,plain,
% 3.11/0.99      ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 3.11/0.99      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
% 3.11/0.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_3677]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_11,plain,
% 3.11/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.11/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.11/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.11/0.99      | ~ v3_pre_topc(X5,X0)
% 3.11/0.99      | ~ m1_pre_topc(X4,X0)
% 3.11/0.99      | ~ r2_hidden(X3,X5)
% 3.11/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.11/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.11/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.11/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.11/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | v2_struct_0(X0)
% 3.11/0.99      | v2_struct_0(X4)
% 3.11/0.99      | ~ v1_funct_1(X2)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ l1_pre_topc(X0)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_460,plain,
% 3.11/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.11/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.11/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.11/0.99      | ~ v3_pre_topc(X5,X0)
% 3.11/0.99      | ~ m1_pre_topc(X4,X0)
% 3.11/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.11/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.11/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.11/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.11/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.11/0.99      | v2_struct_0(X0)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | v2_struct_0(X4)
% 3.11/0.99      | ~ v1_funct_1(X2)
% 3.11/0.99      | ~ l1_pre_topc(X0)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X0)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | sK5 != X5
% 3.11/0.99      | sK6 != X3 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_461,plain,
% 3.11/0.99      ( ~ r1_tmap_1(X0,X1,X2,sK6)
% 3.11/0.99      | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
% 3.11/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.11/0.99      | ~ v3_pre_topc(sK5,X0)
% 3.11/0.99      | ~ m1_pre_topc(X3,X0)
% 3.11/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 3.11/0.99      | v2_struct_0(X0)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | v2_struct_0(X3)
% 3.11/0.99      | ~ v1_funct_1(X2)
% 3.11/0.99      | ~ l1_pre_topc(X0)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X0)
% 3.11/0.99      | ~ v2_pre_topc(X1) ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_460]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_483,plain,
% 3.11/0.99      ( ~ r1_tmap_1(X0,X1,X2,sK6)
% 3.11/0.99      | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
% 3.11/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.11/0.99      | ~ v3_pre_topc(sK5,X0)
% 3.11/0.99      | ~ m1_pre_topc(X3,X0)
% 3.11/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 3.11/0.99      | v2_struct_0(X0)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | v2_struct_0(X3)
% 3.11/0.99      | ~ v1_funct_1(X2)
% 3.11/0.99      | ~ l1_pre_topc(X0)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X0)
% 3.11/0.99      | ~ v2_pre_topc(X1) ),
% 3.11/0.99      inference(forward_subsumption_resolution,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_461,c_449]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_742,plain,
% 3.11/0.99      ( ~ r1_tmap_1(X0,X1,X2,sK6)
% 3.11/0.99      | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
% 3.11/0.99      | ~ v3_pre_topc(sK5,X0)
% 3.11/0.99      | ~ m1_pre_topc(X3,X0)
% 3.11/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 3.11/0.99      | v2_struct_0(X0)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | v2_struct_0(X3)
% 3.11/0.99      | ~ v1_funct_1(X2)
% 3.11/0.99      | ~ l1_pre_topc(X0)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X0)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 3.11/0.99      | sK4 != X2 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_483,c_24]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_743,plain,
% 3.11/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 3.11/0.99      | ~ r1_tmap_1(X2,X1,sK4,sK6)
% 3.11/0.99      | ~ v3_pre_topc(sK5,X2)
% 3.11/0.99      | ~ m1_pre_topc(X0,X2)
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 3.11/0.99      | v2_struct_0(X2)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | v2_struct_0(X0)
% 3.11/0.99      | ~ v1_funct_1(sK4)
% 3.11/0.99      | ~ l1_pre_topc(X2)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X2)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_742]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_747,plain,
% 3.11/0.99      ( v2_struct_0(X0)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | v2_struct_0(X2)
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
% 3.11/0.99      | ~ m1_pre_topc(X0,X2)
% 3.11/0.99      | ~ v3_pre_topc(sK5,X2)
% 3.11/0.99      | ~ r1_tmap_1(X2,X1,sK4,sK6)
% 3.11/0.99      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 3.11/0.99      | ~ l1_pre_topc(X2)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X2)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_743,c_25]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_748,plain,
% 3.11/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 3.11/0.99      | ~ r1_tmap_1(X2,X1,sK4,sK6)
% 3.11/0.99      | ~ v3_pre_topc(sK5,X2)
% 3.11/0.99      | ~ m1_pre_topc(X0,X2)
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 3.11/0.99      | v2_struct_0(X0)
% 3.11/0.99      | v2_struct_0(X2)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ l1_pre_topc(X2)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X2)
% 3.11/0.99      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(renaming,[status(thm)],[c_747]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1106,plain,
% 3.11/0.99      ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,sK4,X0_53),sK6)
% 3.11/0.99      | ~ r1_tmap_1(X2_53,X1_53,sK4,sK6)
% 3.11/0.99      | ~ v3_pre_topc(sK5,X2_53)
% 3.11/0.99      | ~ m1_pre_topc(X0_53,X2_53)
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2_53)))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0_53))
% 3.11/0.99      | v2_struct_0(X0_53)
% 3.11/0.99      | v2_struct_0(X2_53)
% 3.11/0.99      | v2_struct_0(X1_53)
% 3.11/0.99      | ~ l1_pre_topc(X1_53)
% 3.11/0.99      | ~ l1_pre_topc(X2_53)
% 3.11/0.99      | ~ v2_pre_topc(X1_53)
% 3.11/0.99      | ~ v2_pre_topc(X2_53)
% 3.11/0.99      | u1_struct_0(X2_53) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(subtyping,[status(esa)],[c_748]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2662,plain,
% 3.11/0.99      ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK3,X1_53,sK4,X0_53),sK6)
% 3.11/0.99      | ~ r1_tmap_1(sK3,X1_53,sK4,sK6)
% 3.11/0.99      | ~ v3_pre_topc(sK5,sK3)
% 3.11/0.99      | ~ m1_pre_topc(X0_53,sK3)
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0_53))
% 3.11/0.99      | v2_struct_0(X0_53)
% 3.11/0.99      | v2_struct_0(X1_53)
% 3.11/0.99      | v2_struct_0(sK3)
% 3.11/0.99      | ~ l1_pre_topc(X1_53)
% 3.11/0.99      | ~ l1_pre_topc(sK3)
% 3.11/0.99      | ~ v2_pre_topc(X1_53)
% 3.11/0.99      | ~ v2_pre_topc(sK3)
% 3.11/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK0)
% 3.11/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1106]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3874,plain,
% 3.11/0.99      ( ~ r1_tmap_1(sK3,X0_53,sK4,sK6)
% 3.11/0.99      | r1_tmap_1(sK2,X0_53,k2_tmap_1(sK3,X0_53,sK4,sK2),sK6)
% 3.11/0.99      | ~ v3_pre_topc(sK5,sK3)
% 3.11/0.99      | ~ m1_pre_topc(sK2,sK3)
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.11/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 3.11/0.99      | v2_struct_0(X0_53)
% 3.11/0.99      | v2_struct_0(sK3)
% 3.11/0.99      | v2_struct_0(sK2)
% 3.11/0.99      | ~ l1_pre_topc(X0_53)
% 3.11/0.99      | ~ l1_pre_topc(sK3)
% 3.11/0.99      | ~ v2_pre_topc(X0_53)
% 3.11/0.99      | ~ v2_pre_topc(sK3)
% 3.11/0.99      | u1_struct_0(X0_53) != u1_struct_0(sK0)
% 3.11/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_2662]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3875,plain,
% 3.11/0.99      ( u1_struct_0(X0_53) != u1_struct_0(sK0)
% 3.11/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.11/0.99      | r1_tmap_1(sK3,X0_53,sK4,sK6) != iProver_top
% 3.11/0.99      | r1_tmap_1(sK2,X0_53,k2_tmap_1(sK3,X0_53,sK4,sK2),sK6) = iProver_top
% 3.11/0.99      | v3_pre_topc(sK5,sK3) != iProver_top
% 3.11/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.11/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.11/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 3.11/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53)))) != iProver_top
% 3.11/0.99      | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
% 3.11/0.99      | v2_struct_0(X0_53) = iProver_top
% 3.11/0.99      | v2_struct_0(sK3) = iProver_top
% 3.11/0.99      | v2_struct_0(sK2) = iProver_top
% 3.11/0.99      | l1_pre_topc(X0_53) != iProver_top
% 3.11/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.11/0.99      | v2_pre_topc(X0_53) != iProver_top
% 3.11/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_3874]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3877,plain,
% 3.11/0.99      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 3.11/0.99      | r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
% 3.11/0.99      | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) = iProver_top
% 3.11/0.99      | v3_pre_topc(sK5,sK3) != iProver_top
% 3.11/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.11/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.11/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 3.11/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 3.11/0.99      | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
% 3.11/0.99      | v2_struct_0(sK3) = iProver_top
% 3.11/0.99      | v2_struct_0(sK0) = iProver_top
% 3.11/0.99      | v2_struct_0(sK2) = iProver_top
% 3.11/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.11/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.11/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.11/0.99      | v2_pre_topc(sK0) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_3875]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_7,plain,
% 3.11/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/0.99      | ~ m1_pre_topc(X3,X1)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | v2_struct_0(X2)
% 3.11/0.99      | ~ v1_funct_1(X0)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ l1_pre_topc(X2)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X2)
% 3.11/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.11/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_634,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.11/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.11/0.99      | v2_struct_0(X3)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | ~ v1_funct_1(X2)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ l1_pre_topc(X3)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X3)
% 3.11/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 3.11/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X3) != u1_struct_0(sK0)
% 3.11/0.99      | sK4 != X2 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_24]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_635,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | v2_struct_0(X2)
% 3.11/0.99      | ~ v1_funct_1(sK4)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ l1_pre_topc(X2)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X2)
% 3.11/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 3.11/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X2) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_634]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_639,plain,
% 3.11/0.99      ( v2_struct_0(X2)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/0.99      | ~ m1_pre_topc(X0,X1)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ l1_pre_topc(X2)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X2)
% 3.11/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 3.11/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X2) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_635,c_25]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_640,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/0.99      | v2_struct_0(X2)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ l1_pre_topc(X2)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X2)
% 3.11/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 3.11/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X2) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(renaming,[status(thm)],[c_639]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1108,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0_53,X1_53)
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X2_53))))
% 3.11/0.99      | v2_struct_0(X2_53)
% 3.11/0.99      | v2_struct_0(X1_53)
% 3.11/0.99      | ~ l1_pre_topc(X1_53)
% 3.11/0.99      | ~ l1_pre_topc(X2_53)
% 3.11/0.99      | ~ v2_pre_topc(X1_53)
% 3.11/0.99      | ~ v2_pre_topc(X2_53)
% 3.11/0.99      | k2_partfun1(u1_struct_0(X1_53),u1_struct_0(X2_53),sK4,u1_struct_0(X0_53)) = k2_tmap_1(X1_53,X2_53,sK4,X0_53)
% 3.11/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X2_53) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(subtyping,[status(esa)],[c_640]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2249,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0_53,sK3)
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
% 3.11/0.99      | v2_struct_0(X1_53)
% 3.11/0.99      | v2_struct_0(sK3)
% 3.11/0.99      | ~ l1_pre_topc(X1_53)
% 3.11/0.99      | ~ l1_pre_topc(sK3)
% 3.11/0.99      | ~ v2_pre_topc(X1_53)
% 3.11/0.99      | ~ v2_pre_topc(sK3)
% 3.11/0.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1_53),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK3,X1_53,sK4,X0_53)
% 3.11/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK0)
% 3.11/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1108]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3481,plain,
% 3.11/0.99      ( ~ m1_pre_topc(sK2,sK3)
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 3.11/0.99      | v2_struct_0(X0_53)
% 3.11/0.99      | v2_struct_0(sK3)
% 3.11/0.99      | ~ l1_pre_topc(X0_53)
% 3.11/0.99      | ~ l1_pre_topc(sK3)
% 3.11/0.99      | ~ v2_pre_topc(X0_53)
% 3.11/0.99      | ~ v2_pre_topc(sK3)
% 3.11/0.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0_53),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,X0_53,sK4,sK2)
% 3.11/0.99      | u1_struct_0(X0_53) != u1_struct_0(sK0)
% 3.11/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_2249]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3483,plain,
% 3.11/0.99      ( ~ m1_pre_topc(sK2,sK3)
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
% 3.11/0.99      | v2_struct_0(sK3)
% 3.11/0.99      | v2_struct_0(sK0)
% 3.11/0.99      | ~ l1_pre_topc(sK3)
% 3.11/0.99      | ~ l1_pre_topc(sK0)
% 3.11/0.99      | ~ v2_pre_topc(sK3)
% 3.11/0.99      | ~ v2_pre_topc(sK0)
% 3.11/0.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK0,sK4,sK2)
% 3.11/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_3481]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3446,plain,
% 3.11/0.99      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1140]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1,plain,
% 3.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1137,plain,
% 3.11/0.99      ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 3.11/0.99      | ~ r1_tarski(X0_54,X1_54) ),
% 3.11/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3427,plain,
% 3.11/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(sK3)) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1137]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3428,plain,
% 3.11/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.11/0.99      | r1_tarski(sK5,u1_struct_0(sK3)) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_3427]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_0,plain,
% 3.11/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1138,plain,
% 3.11/0.99      ( ~ r1_tarski(X0_54,X1_54)
% 3.11/0.99      | ~ r1_tarski(X2_54,X0_54)
% 3.11/0.99      | r1_tarski(X2_54,X1_54) ),
% 3.11/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3009,plain,
% 3.11/0.99      ( r1_tarski(X0_54,u1_struct_0(sK3))
% 3.11/0.99      | ~ r1_tarski(X0_54,u1_struct_0(sK2))
% 3.11/0.99      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1138]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3291,plain,
% 3.11/0.99      ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
% 3.11/0.99      | r1_tarski(sK5,u1_struct_0(sK3))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(sK2)) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_3009]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3292,plain,
% 3.11/0.99      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.11/0.99      | r1_tarski(sK5,u1_struct_0(sK3)) = iProver_top
% 3.11/0.99      | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_3291]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | v2_pre_topc(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1135,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0_53,X1_53)
% 3.11/0.99      | ~ l1_pre_topc(X1_53)
% 3.11/0.99      | ~ v2_pre_topc(X1_53)
% 3.11/0.99      | v2_pre_topc(X0_53) ),
% 3.11/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2998,plain,
% 3.11/0.99      ( ~ m1_pre_topc(sK3,X0_53)
% 3.11/0.99      | ~ l1_pre_topc(X0_53)
% 3.11/0.99      | ~ v2_pre_topc(X0_53)
% 3.11/0.99      | v2_pre_topc(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1135]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3086,plain,
% 3.11/0.99      ( ~ m1_pre_topc(sK3,sK1)
% 3.11/0.99      | ~ l1_pre_topc(sK1)
% 3.11/0.99      | v2_pre_topc(sK3)
% 3.11/0.99      | ~ v2_pre_topc(sK1) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_2998]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3087,plain,
% 3.11/0.99      ( m1_pre_topc(sK3,sK1) != iProver_top
% 3.11/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.11/0.99      | v2_pre_topc(sK3) = iProver_top
% 3.11/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_3086]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_8,plain,
% 3.11/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/0.99      | ~ m1_pre_topc(X1,X3)
% 3.11/0.99      | ~ m1_pre_topc(X4,X3)
% 3.11/0.99      | ~ m1_pre_topc(X4,X1)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/0.99      | v2_struct_0(X3)
% 3.11/0.99      | v2_struct_0(X2)
% 3.11/0.99      | ~ v1_funct_1(X0)
% 3.11/0.99      | ~ l1_pre_topc(X3)
% 3.11/0.99      | ~ l1_pre_topc(X2)
% 3.11/0.99      | ~ v2_pre_topc(X3)
% 3.11/0.99      | ~ v2_pre_topc(X2)
% 3.11/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X4)) = k3_tmap_1(X3,X2,X1,X4,X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_583,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.11/0.99      | ~ m1_pre_topc(X2,X1)
% 3.11/0.99      | ~ m1_pre_topc(X2,X0)
% 3.11/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X4))))
% 3.11/0.99      | v2_struct_0(X4)
% 3.11/0.99      | v2_struct_0(X1)
% 3.11/0.99      | ~ v1_funct_1(X3)
% 3.11/0.99      | ~ l1_pre_topc(X4)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X4)
% 3.11/0.99      | ~ v2_pre_topc(X1)
% 3.11/0.99      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X4),X3,u1_struct_0(X2)) = k3_tmap_1(X1,X4,X0,X2,X3)
% 3.11/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X4) != u1_struct_0(sK0)
% 3.11/0.99      | sK4 != X3 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_584,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.11/0.99      | ~ m1_pre_topc(X1,X2)
% 3.11/0.99      | ~ m1_pre_topc(X0,X2)
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.11/0.99      | v2_struct_0(X2)
% 3.11/0.99      | v2_struct_0(X3)
% 3.11/0.99      | ~ v1_funct_1(sK4)
% 3.11/0.99      | ~ l1_pre_topc(X2)
% 3.11/0.99      | ~ l1_pre_topc(X3)
% 3.11/0.99      | ~ v2_pre_topc(X2)
% 3.11/0.99      | ~ v2_pre_topc(X3)
% 3.11/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 3.11/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X3) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_583]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_588,plain,
% 3.11/0.99      ( v2_struct_0(X3)
% 3.11/0.99      | v2_struct_0(X2)
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.11/0.99      | ~ m1_pre_topc(X0,X2)
% 3.11/0.99      | ~ m1_pre_topc(X1,X2)
% 3.11/0.99      | ~ m1_pre_topc(X0,X1)
% 3.11/0.99      | ~ l1_pre_topc(X2)
% 3.11/0.99      | ~ l1_pre_topc(X3)
% 3.11/0.99      | ~ v2_pre_topc(X2)
% 3.11/0.99      | ~ v2_pre_topc(X3)
% 3.11/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 3.11/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X3) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_584,c_25]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_589,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.11/0.99      | ~ m1_pre_topc(X1,X2)
% 3.11/0.99      | ~ m1_pre_topc(X0,X2)
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.11/0.99      | v2_struct_0(X2)
% 3.11/0.99      | v2_struct_0(X3)
% 3.11/0.99      | ~ l1_pre_topc(X2)
% 3.11/0.99      | ~ l1_pre_topc(X3)
% 3.11/0.99      | ~ v2_pre_topc(X2)
% 3.11/0.99      | ~ v2_pre_topc(X3)
% 3.11/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 3.11/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X3) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(renaming,[status(thm)],[c_588]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_12,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.11/0.99      | ~ m1_pre_topc(X2,X0)
% 3.11/0.99      | m1_pre_topc(X2,X1)
% 3.11/0.99      | ~ l1_pre_topc(X1)
% 3.11/0.99      | ~ v2_pre_topc(X1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_620,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.11/0.99      | ~ m1_pre_topc(X1,X2)
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.11/0.99      | v2_struct_0(X2)
% 3.11/0.99      | v2_struct_0(X3)
% 3.11/0.99      | ~ l1_pre_topc(X2)
% 3.11/0.99      | ~ l1_pre_topc(X3)
% 3.11/0.99      | ~ v2_pre_topc(X2)
% 3.11/0.99      | ~ v2_pre_topc(X3)
% 3.11/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 3.11/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X3) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(forward_subsumption_resolution,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_589,c_12]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1109,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0_53,X1_53)
% 3.11/0.99      | ~ m1_pre_topc(X1_53,X2_53)
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X3_53))))
% 3.11/0.99      | v2_struct_0(X2_53)
% 3.11/0.99      | v2_struct_0(X3_53)
% 3.11/0.99      | ~ l1_pre_topc(X2_53)
% 3.11/0.99      | ~ l1_pre_topc(X3_53)
% 3.11/0.99      | ~ v2_pre_topc(X2_53)
% 3.11/0.99      | ~ v2_pre_topc(X3_53)
% 3.11/0.99      | k2_partfun1(u1_struct_0(X1_53),u1_struct_0(X3_53),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X2_53,X3_53,X1_53,X0_53,sK4)
% 3.11/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(X3_53) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(subtyping,[status(esa)],[c_620]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2248,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0_53,sK3)
% 3.11/0.99      | ~ m1_pre_topc(sK3,X1_53)
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2_53))))
% 3.11/0.99      | v2_struct_0(X2_53)
% 3.11/0.99      | v2_struct_0(X1_53)
% 3.11/0.99      | ~ l1_pre_topc(X1_53)
% 3.11/0.99      | ~ l1_pre_topc(X2_53)
% 3.11/0.99      | ~ v2_pre_topc(X1_53)
% 3.11/0.99      | ~ v2_pre_topc(X2_53)
% 3.11/0.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X2_53),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,X2_53,sK3,X0_53,sK4)
% 3.11/0.99      | u1_struct_0(X2_53) != u1_struct_0(sK0)
% 3.11/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1109]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2656,plain,
% 3.11/0.99      ( ~ m1_pre_topc(sK3,X0_53)
% 3.11/0.99      | ~ m1_pre_topc(sK2,sK3)
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
% 3.11/0.99      | v2_struct_0(X0_53)
% 3.11/0.99      | v2_struct_0(X1_53)
% 3.11/0.99      | ~ l1_pre_topc(X1_53)
% 3.11/0.99      | ~ l1_pre_topc(X0_53)
% 3.11/0.99      | ~ v2_pre_topc(X1_53)
% 3.11/0.99      | ~ v2_pre_topc(X0_53)
% 3.11/0.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1_53),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0_53,X1_53,sK3,sK2,sK4)
% 3.11/0.99      | u1_struct_0(X1_53) != u1_struct_0(sK0)
% 3.11/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_2248]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3064,plain,
% 3.11/0.99      ( ~ m1_pre_topc(sK3,sK1)
% 3.11/0.99      | ~ m1_pre_topc(sK2,sK3)
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 3.11/0.99      | v2_struct_0(X0_53)
% 3.11/0.99      | v2_struct_0(sK1)
% 3.11/0.99      | ~ l1_pre_topc(X0_53)
% 3.11/0.99      | ~ l1_pre_topc(sK1)
% 3.11/0.99      | ~ v2_pre_topc(X0_53)
% 3.11/0.99      | ~ v2_pre_topc(sK1)
% 3.11/0.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0_53),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK1,X0_53,sK3,sK2,sK4)
% 3.11/0.99      | u1_struct_0(X0_53) != u1_struct_0(sK0)
% 3.11/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_2656]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3066,plain,
% 3.11/0.99      ( ~ m1_pre_topc(sK3,sK1)
% 3.11/0.99      | ~ m1_pre_topc(sK2,sK3)
% 3.11/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
% 3.11/0.99      | v2_struct_0(sK1)
% 3.11/0.99      | v2_struct_0(sK0)
% 3.11/0.99      | ~ l1_pre_topc(sK1)
% 3.11/0.99      | ~ l1_pre_topc(sK0)
% 3.11/0.99      | ~ v2_pre_topc(sK1)
% 3.11/0.99      | ~ v2_pre_topc(sK0)
% 3.11/0.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 3.11/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.11/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_3064]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1149,plain,
% 3.11/0.99      ( X0_54 != X1_54
% 3.11/0.99      | k3_tmap_1(X0_53,X1_53,X2_53,X3_53,X0_54) = k3_tmap_1(X0_53,X1_53,X2_53,X3_53,X1_54) ),
% 3.11/0.99      theory(equality) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3053,plain,
% 3.11/0.99      ( X0_54 != sK4
% 3.11/0.99      | k3_tmap_1(sK1,sK0,sK3,sK2,X0_54) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1149]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3056,plain,
% 3.11/0.99      ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 3.11/0.99      | sK4 != sK4 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_3053]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2513,plain,
% 3.11/0.99      ( X0_54 != X1_54 | X0_54 = sK6 | sK6 != X1_54 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1141]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2788,plain,
% 3.11/0.99      ( X0_54 = sK6 | X0_54 != sK7 | sK6 != sK7 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_2513]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3007,plain,
% 3.11/0.99      ( sK6 != sK7 | sK7 = sK6 | sK7 != sK7 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_2788]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1134,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0_53,X1_53)
% 3.11/0.99      | ~ l1_pre_topc(X1_53)
% 3.11/0.99      | l1_pre_topc(X0_53) ),
% 3.11/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2477,plain,
% 3.11/0.99      ( ~ m1_pre_topc(sK3,X0_53)
% 3.11/0.99      | ~ l1_pre_topc(X0_53)
% 3.11/0.99      | l1_pre_topc(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1134]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2746,plain,
% 3.11/0.99      ( ~ m1_pre_topc(sK3,sK1) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK1) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_2477]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2747,plain,
% 3.11/0.99      ( m1_pre_topc(sK3,sK1) != iProver_top
% 3.11/0.99      | l1_pre_topc(sK3) = iProver_top
% 3.11/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_2746]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2500,plain,
% 3.11/0.99      ( sK7 = sK7 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1140]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_6,plain,
% 3.11/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.11/0.99      | v3_pre_topc(X0,X2)
% 3.11/0.99      | ~ m1_pre_topc(X2,X1)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.11/0.99      | ~ l1_pre_topc(X1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1133,plain,
% 3.11/0.99      ( ~ v3_pre_topc(X0_54,X0_53)
% 3.11/0.99      | v3_pre_topc(X0_54,X1_53)
% 3.11/0.99      | ~ m1_pre_topc(X1_53,X0_53)
% 3.11/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X1_53)))
% 3.11/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 3.11/0.99      | ~ l1_pre_topc(X0_53) ),
% 3.11/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2336,plain,
% 3.11/0.99      ( v3_pre_topc(sK5,X0_53)
% 3.11/0.99      | ~ v3_pre_topc(sK5,sK1)
% 3.11/0.99      | ~ m1_pre_topc(X0_53,sK1)
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53)))
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.11/0.99      | ~ l1_pre_topc(sK1) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1133]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2470,plain,
% 3.11/0.99      ( v3_pre_topc(sK5,sK3)
% 3.11/0.99      | ~ v3_pre_topc(sK5,sK1)
% 3.11/0.99      | ~ m1_pre_topc(sK3,sK1)
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.11/0.99      | ~ l1_pre_topc(sK1) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_2336]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2471,plain,
% 3.11/0.99      ( v3_pre_topc(sK5,sK3) = iProver_top
% 3.11/0.99      | v3_pre_topc(sK5,sK1) != iProver_top
% 3.11/0.99      | m1_pre_topc(sK3,sK1) != iProver_top
% 3.11/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.11/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.11/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_2470]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1136,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 3.11/0.99      | r1_tarski(X0_54,X1_54) ),
% 3.11/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2380,plain,
% 3.11/0.99      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.11/0.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1136]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2381,plain,
% 3.11/0.99      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.11/0.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_2380]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1110,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0_54)) | m1_subset_1(sK6,X0_54) ),
% 3.11/0.99      inference(subtyping,[status(esa)],[c_449]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2371,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.11/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1110]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2372,plain,
% 3.11/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.11/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_2371]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_9,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.11/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.11/0.99      | ~ l1_pre_topc(X1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1132,plain,
% 3.11/0.99      ( ~ m1_pre_topc(X0_53,X1_53)
% 3.11/0.99      | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53)))
% 3.11/0.99      | ~ l1_pre_topc(X1_53) ),
% 3.11/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2271,plain,
% 3.11/0.99      ( ~ m1_pre_topc(sK2,sK3)
% 3.11/0.99      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.11/0.99      | ~ l1_pre_topc(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1132]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2272,plain,
% 3.11/0.99      ( m1_pre_topc(sK2,sK3) != iProver_top
% 3.11/0.99      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.11/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_2271]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2264,plain,
% 3.11/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.11/0.99      | ~ r1_tarski(sK5,u1_struct_0(sK2)) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1137]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2265,plain,
% 3.11/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.11/0.99      | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_2264]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2247,plain,
% 3.11/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1140]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_15,negated_conjecture,
% 3.11/0.99      ( sK6 = sK7 ),
% 3.11/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1128,negated_conjecture,
% 3.11/0.99      ( sK6 = sK7 ),
% 3.11/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1161,plain,
% 3.11/0.99      ( sK4 = sK4 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1140]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_13,negated_conjecture,
% 3.11/0.99      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 3.11/0.99      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 3.11/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_57,plain,
% 3.11/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
% 3.11/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_14,negated_conjecture,
% 3.11/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK6)
% 3.11/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 3.11/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_56,plain,
% 3.11/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 3.11/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_16,negated_conjecture,
% 3.11/0.99      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 3.11/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_55,plain,
% 3.11/0.99      ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_18,negated_conjecture,
% 3.11/0.99      ( v3_pre_topc(sK5,sK1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_53,plain,
% 3.11/0.99      ( v3_pre_topc(sK5,sK1) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_21,negated_conjecture,
% 3.11/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.11/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_50,plain,
% 3.11/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_22,negated_conjecture,
% 3.11/0.99      ( m1_pre_topc(sK2,sK3) ),
% 3.11/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_49,plain,
% 3.11/0.99      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_23,negated_conjecture,
% 3.11/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
% 3.11/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_48,plain,
% 3.11/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_26,negated_conjecture,
% 3.11/0.99      ( m1_pre_topc(sK3,sK1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_45,plain,
% 3.11/0.99      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_27,negated_conjecture,
% 3.11/0.99      ( ~ v2_struct_0(sK3) ),
% 3.11/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_44,plain,
% 3.11/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_29,negated_conjecture,
% 3.11/0.99      ( ~ v2_struct_0(sK2) ),
% 3.11/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_42,plain,
% 3.11/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_30,negated_conjecture,
% 3.11/0.99      ( l1_pre_topc(sK1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_41,plain,
% 3.11/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_31,negated_conjecture,
% 3.11/0.99      ( v2_pre_topc(sK1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_40,plain,
% 3.11/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_32,negated_conjecture,
% 3.11/0.99      ( ~ v2_struct_0(sK1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_33,negated_conjecture,
% 3.11/0.99      ( l1_pre_topc(sK0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_38,plain,
% 3.11/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_34,negated_conjecture,
% 3.11/0.99      ( v2_pre_topc(sK0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_37,plain,
% 3.11/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_35,negated_conjecture,
% 3.11/0.99      ( ~ v2_struct_0(sK0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_36,plain,
% 3.11/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(contradiction,plain,
% 3.11/0.99      ( $false ),
% 3.11/0.99      inference(minisat,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_6874,c_6433,c_6065,c_5627,c_5626,c_5277,c_4360,c_4018,
% 3.11/0.99                 c_3877,c_3483,c_3446,c_3428,c_3292,c_3087,c_3086,c_3066,
% 3.11/0.99                 c_3056,c_3007,c_2747,c_2746,c_2500,c_2471,c_2381,c_2372,
% 3.11/0.99                 c_2272,c_2265,c_2247,c_1128,c_1161,c_57,c_56,c_55,c_53,
% 3.11/0.99                 c_50,c_49,c_22,c_48,c_23,c_45,c_26,c_44,c_27,c_42,c_41,
% 3.11/0.99                 c_30,c_40,c_31,c_32,c_38,c_33,c_37,c_34,c_36,c_35]) ).
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  ------                               Statistics
% 3.11/0.99  
% 3.11/0.99  ------ General
% 3.11/0.99  
% 3.11/0.99  abstr_ref_over_cycles:                  0
% 3.11/0.99  abstr_ref_under_cycles:                 0
% 3.11/0.99  gc_basic_clause_elim:                   0
% 3.11/0.99  forced_gc_time:                         0
% 3.11/0.99  parsing_time:                           0.011
% 3.11/0.99  unif_index_cands_time:                  0.
% 3.11/0.99  unif_index_add_time:                    0.
% 3.11/0.99  orderings_time:                         0.
% 3.11/0.99  out_proof_time:                         0.015
% 3.11/0.99  total_time:                             0.234
% 3.11/0.99  num_of_symbols:                         58
% 3.11/0.99  num_of_terms:                           3040
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing
% 3.11/0.99  
% 3.11/0.99  num_of_splits:                          0
% 3.11/0.99  num_of_split_atoms:                     0
% 3.11/0.99  num_of_reused_defs:                     0
% 3.11/0.99  num_eq_ax_congr_red:                    24
% 3.11/0.99  num_of_sem_filtered_clauses:            1
% 3.11/0.99  num_of_subtypes:                        2
% 3.11/0.99  monotx_restored_types:                  0
% 3.11/0.99  sat_num_of_epr_types:                   0
% 3.11/0.99  sat_num_of_non_cyclic_types:            0
% 3.11/0.99  sat_guarded_non_collapsed_types:        0
% 3.11/0.99  num_pure_diseq_elim:                    0
% 3.11/0.99  simp_replaced_by:                       0
% 3.11/0.99  res_preprocessed:                       158
% 3.11/0.99  prep_upred:                             0
% 3.11/0.99  prep_unflattend:                        10
% 3.11/0.99  smt_new_axioms:                         0
% 3.11/0.99  pred_elim_cands:                        8
% 3.11/0.99  pred_elim:                              3
% 3.11/0.99  pred_elim_cl:                           3
% 3.11/0.99  pred_elim_cycles:                       5
% 3.11/0.99  merged_defs:                            16
% 3.11/0.99  merged_defs_ncl:                        0
% 3.11/0.99  bin_hyper_res:                          16
% 3.11/0.99  prep_cycles:                            4
% 3.11/0.99  pred_elim_time:                         0.015
% 3.11/0.99  splitting_time:                         0.
% 3.11/0.99  sem_filter_time:                        0.
% 3.11/0.99  monotx_time:                            0.
% 3.11/0.99  subtype_inf_time:                       0.
% 3.11/0.99  
% 3.11/0.99  ------ Problem properties
% 3.11/0.99  
% 3.11/0.99  clauses:                                33
% 3.11/0.99  conjectures:                            20
% 3.11/0.99  epr:                                    17
% 3.11/0.99  horn:                                   28
% 3.11/0.99  ground:                                 20
% 3.11/0.99  unary:                                  18
% 3.11/0.99  binary:                                 5
% 3.11/0.99  lits:                                   109
% 3.11/0.99  lits_eq:                                11
% 3.11/0.99  fd_pure:                                0
% 3.11/0.99  fd_pseudo:                              0
% 3.11/0.99  fd_cond:                                0
% 3.11/0.99  fd_pseudo_cond:                         0
% 3.11/0.99  ac_symbols:                             0
% 3.11/0.99  
% 3.11/0.99  ------ Propositional Solver
% 3.11/0.99  
% 3.11/0.99  prop_solver_calls:                      32
% 3.11/0.99  prop_fast_solver_calls:                 1720
% 3.11/0.99  smt_solver_calls:                       0
% 3.11/0.99  smt_fast_solver_calls:                  0
% 3.11/0.99  prop_num_of_clauses:                    1686
% 3.11/0.99  prop_preprocess_simplified:             5639
% 3.11/0.99  prop_fo_subsumed:                       53
% 3.11/0.99  prop_solver_time:                       0.
% 3.11/0.99  smt_solver_time:                        0.
% 3.11/0.99  smt_fast_solver_time:                   0.
% 3.11/0.99  prop_fast_solver_time:                  0.
% 3.11/0.99  prop_unsat_core_time:                   0.
% 3.11/0.99  
% 3.11/0.99  ------ QBF
% 3.11/0.99  
% 3.11/0.99  qbf_q_res:                              0
% 3.11/0.99  qbf_num_tautologies:                    0
% 3.11/0.99  qbf_prep_cycles:                        0
% 3.11/0.99  
% 3.11/0.99  ------ BMC1
% 3.11/0.99  
% 3.11/0.99  bmc1_current_bound:                     -1
% 3.11/0.99  bmc1_last_solved_bound:                 -1
% 3.11/0.99  bmc1_unsat_core_size:                   -1
% 3.11/0.99  bmc1_unsat_core_parents_size:           -1
% 3.11/0.99  bmc1_merge_next_fun:                    0
% 3.11/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.11/0.99  
% 3.11/0.99  ------ Instantiation
% 3.11/0.99  
% 3.11/0.99  inst_num_of_clauses:                    542
% 3.11/0.99  inst_num_in_passive:                    67
% 3.11/0.99  inst_num_in_active:                     458
% 3.11/0.99  inst_num_in_unprocessed:                17
% 3.11/0.99  inst_num_of_loops:                      550
% 3.11/0.99  inst_num_of_learning_restarts:          0
% 3.11/0.99  inst_num_moves_active_passive:          81
% 3.11/0.99  inst_lit_activity:                      0
% 3.11/0.99  inst_lit_activity_moves:                0
% 3.11/0.99  inst_num_tautologies:                   0
% 3.11/0.99  inst_num_prop_implied:                  0
% 3.11/0.99  inst_num_existing_simplified:           0
% 3.11/0.99  inst_num_eq_res_simplified:             0
% 3.11/0.99  inst_num_child_elim:                    0
% 3.11/0.99  inst_num_of_dismatching_blockings:      73
% 3.11/0.99  inst_num_of_non_proper_insts:           704
% 3.11/0.99  inst_num_of_duplicates:                 0
% 3.11/0.99  inst_inst_num_from_inst_to_res:         0
% 3.11/0.99  inst_dismatching_checking_time:         0.
% 3.11/0.99  
% 3.11/0.99  ------ Resolution
% 3.11/0.99  
% 3.11/0.99  res_num_of_clauses:                     0
% 3.11/0.99  res_num_in_passive:                     0
% 3.11/0.99  res_num_in_active:                      0
% 3.11/0.99  res_num_of_loops:                       162
% 3.11/0.99  res_forward_subset_subsumed:            130
% 3.11/0.99  res_backward_subset_subsumed:           0
% 3.11/0.99  res_forward_subsumed:                   0
% 3.11/0.99  res_backward_subsumed:                  0
% 3.11/0.99  res_forward_subsumption_resolution:     3
% 3.11/0.99  res_backward_subsumption_resolution:    0
% 3.11/0.99  res_clause_to_clause_subsumption:       853
% 3.11/0.99  res_orphan_elimination:                 0
% 3.11/0.99  res_tautology_del:                      222
% 3.11/0.99  res_num_eq_res_simplified:              0
% 3.11/0.99  res_num_sel_changes:                    0
% 3.11/0.99  res_moves_from_active_to_pass:          0
% 3.11/0.99  
% 3.11/0.99  ------ Superposition
% 3.11/0.99  
% 3.11/0.99  sup_time_total:                         0.
% 3.11/0.99  sup_time_generating:                    0.
% 3.11/0.99  sup_time_sim_full:                      0.
% 3.11/0.99  sup_time_sim_immed:                     0.
% 3.11/0.99  
% 3.11/0.99  sup_num_of_clauses:                     146
% 3.11/0.99  sup_num_in_active:                      107
% 3.11/0.99  sup_num_in_passive:                     39
% 3.11/0.99  sup_num_of_loops:                       108
% 3.11/0.99  sup_fw_superposition:                   131
% 3.11/0.99  sup_bw_superposition:                   123
% 3.11/0.99  sup_immediate_simplified:               133
% 3.11/0.99  sup_given_eliminated:                   0
% 3.11/0.99  comparisons_done:                       0
% 3.11/0.99  comparisons_avoided:                    0
% 3.11/0.99  
% 3.11/0.99  ------ Simplifications
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  sim_fw_subset_subsumed:                 96
% 3.11/0.99  sim_bw_subset_subsumed:                 2
% 3.11/0.99  sim_fw_subsumed:                        36
% 3.11/0.99  sim_bw_subsumed:                        1
% 3.11/0.99  sim_fw_subsumption_res:                 5
% 3.11/0.99  sim_bw_subsumption_res:                 0
% 3.11/0.99  sim_tautology_del:                      2
% 3.11/0.99  sim_eq_tautology_del:                   0
% 3.11/0.99  sim_eq_res_simp:                        0
% 3.11/0.99  sim_fw_demodulated:                     0
% 3.11/0.99  sim_bw_demodulated:                     0
% 3.11/0.99  sim_light_normalised:                   6
% 3.11/0.99  sim_joinable_taut:                      0
% 3.11/0.99  sim_joinable_simp:                      0
% 3.11/0.99  sim_ac_normalised:                      0
% 3.11/0.99  sim_smt_subsumption:                    0
% 3.11/0.99  
%------------------------------------------------------------------------------
