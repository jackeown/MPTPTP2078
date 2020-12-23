%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:13 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 603 expanded)
%              Number of clauses        :  105 ( 121 expanded)
%              Number of leaves         :   20 ( 272 expanded)
%              Depth                    :   21
%              Number of atoms          : 1451 (13021 expanded)
%              Number of equality atoms :  144 ( 785 expanded)
%              Maximal formula depth    :   32 (   9 average)
%              Maximal clause size      :   50 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(flattening,[],[f29])).

fof(f34,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(nnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X6)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(equality_resolution,[],[f57])).

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

fof(f31,plain,(
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
    inference(flattening,[],[f31])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f32])).

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
    inference(flattening,[],[f35])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f36,f44,f43,f42,f41,f40,f39,f38,f37])).

fof(f77,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(equality_resolution,[],[f58])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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
    inference(ennf_transformation,[],[f5])).

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

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f80,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r2_hidden(X3,X6)
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_452,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | sK5 != X6
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_453,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK6)
    | r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X0,X4)
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_499,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK6)
    | r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X0,X4)
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_453,c_10])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_664,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK6)
    | r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X0,X4)
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_499,c_24])).

cnf(c_665,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | ~ r1_tmap_1(X3,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_669,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ v3_pre_topc(sK5,X3)
    | ~ r1_tmap_1(X3,X1,sK4,sK6)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_665,c_25])).

cnf(c_670,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | ~ r1_tmap_1(X3,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
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
    inference(renaming,[status(thm)],[c_669])).

cnf(c_1657,plain,
    ( r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),sK6)
    | ~ r1_tmap_1(X3_53,X1_53,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3_53)
    | ~ m1_pre_topc(X3_53,X2_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ r1_tarski(sK5,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_53)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK6,u1_struct_0(X3_53))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X3_53)
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X3_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_670])).

cnf(c_3052,plain,
    ( r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,sK3,X0_53,sK4),sK6)
    | ~ r1_tmap_1(sK3,X1_53,sK4,sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(X0_53,sK3)
    | ~ m1_pre_topc(sK3,X2_53)
    | ~ r1_tarski(sK5,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X1_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1657])).

cnf(c_3405,plain,
    ( ~ r1_tmap_1(sK3,X0_53,sK4,sK6)
    | r1_tmap_1(sK2,X0_53,k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4),sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK3,X1_53)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X0_53)
    | u1_struct_0(X0_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3052])).

cnf(c_4907,plain,
    ( ~ r1_tmap_1(sK3,X0_53,sK4,sK6)
    | r1_tmap_1(sK2,X0_53,k3_tmap_1(sK1,X0_53,sK3,sK2,sK4),sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3405])).

cnf(c_4909,plain,
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
    inference(instantiation,[status(thm)],[c_4907])).

cnf(c_11,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r2_hidden(X3,X6)
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_521,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | sK5 != X6
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_522,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X0,X4)
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_568,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X0,X4)
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_522,c_10])).

cnf(c_592,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X0,X4)
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_568,c_24])).

cnf(c_593,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | r1_tmap_1(X3,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_597,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ v3_pre_topc(sK5,X3)
    | r1_tmap_1(X3,X1,sK4,sK6)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_593,c_25])).

cnf(c_598,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | r1_tmap_1(X3,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
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
    inference(renaming,[status(thm)],[c_597])).

cnf(c_1658,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),sK6)
    | r1_tmap_1(X3_53,X1_53,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3_53)
    | ~ m1_pre_topc(X3_53,X2_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ r1_tarski(sK5,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_53)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK6,u1_struct_0(X3_53))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X3_53)
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X3_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_598])).

cnf(c_3051,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,sK3,X0_53,sK4),sK6)
    | r1_tmap_1(sK3,X1_53,sK4,sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(X0_53,sK3)
    | ~ m1_pre_topc(sK3,X2_53)
    | ~ r1_tarski(sK5,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X1_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1658])).

cnf(c_4441,plain,
    ( r1_tmap_1(sK3,X0_53,sK4,sK6)
    | ~ r1_tmap_1(sK2,X0_53,k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4),sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK3,X1_53)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X0_53)
    | u1_struct_0(X0_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3051])).

cnf(c_4742,plain,
    ( r1_tmap_1(sK3,X0_53,sK4,sK6)
    | ~ r1_tmap_1(sK2,X0_53,k3_tmap_1(sK1,X0_53,sK3,sK2,sK4),sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4441])).

cnf(c_4744,plain,
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
    inference(instantiation,[status(thm)],[c_4742])).

cnf(c_1700,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,X0_54,X1_54)
    | r1_tmap_1(X0_53,X1_53,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_3722,plain,
    ( r1_tmap_1(sK2,X0_53,X0_54,X1_54)
    | ~ r1_tmap_1(sK2,X0_53,k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4),sK6)
    | X0_54 != k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4)
    | X1_54 != sK6 ),
    inference(instantiation,[status(thm)],[c_1700])).

cnf(c_3895,plain,
    ( r1_tmap_1(sK2,X0_53,X0_54,sK7)
    | ~ r1_tmap_1(sK2,X0_53,k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4),sK6)
    | X0_54 != k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4)
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_3722])).

cnf(c_4523,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X0_54),sK7)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | k3_tmap_1(sK1,sK0,sK3,sK2,X0_54) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_3895])).

cnf(c_4525,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_4523])).

cnf(c_3824,plain,
    ( r1_tmap_1(sK3,sK0,X0_54,X1_54)
    | ~ r1_tmap_1(sK3,sK0,X2_54,sK7)
    | X0_54 != X2_54
    | X1_54 != sK7 ),
    inference(instantiation,[status(thm)],[c_1700])).

cnf(c_4479,plain,
    ( r1_tmap_1(sK3,sK0,X0_54,sK6)
    | ~ r1_tmap_1(sK3,sK0,X1_54,sK7)
    | X0_54 != X1_54
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_3824])).

cnf(c_4481,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK7)
    | sK6 != sK7
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4479])).

cnf(c_1689,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_3813,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1689])).

cnf(c_3338,plain,
    ( r1_tmap_1(sK3,sK0,X0_54,X1_54)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | X1_54 != sK6
    | X0_54 != sK4 ),
    inference(instantiation,[status(thm)],[c_1700])).

cnf(c_3798,plain,
    ( r1_tmap_1(sK3,sK0,X0_54,sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | X0_54 != sK4
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_3338])).

cnf(c_3800,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK7)
    | sK7 != sK6
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3798])).

cnf(c_1690,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_2994,plain,
    ( X0_54 != X1_54
    | X0_54 = sK6
    | sK6 != X1_54 ),
    inference(instantiation,[status(thm)],[c_1690])).

cnf(c_3213,plain,
    ( X0_54 = sK6
    | X0_54 != sK7
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2994])).

cnf(c_3302,plain,
    ( sK6 != sK7
    | sK7 = sK6
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3213])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1683,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3046,plain,
    ( ~ m1_pre_topc(sK3,X0_53)
    | ~ l1_pre_topc(X0_53)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1683])).

cnf(c_3256,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3046])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1682,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X1_53)))
    | ~ l1_pre_topc(X1_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2936,plain,
    ( ~ m1_pre_topc(sK2,X0_53)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X0_53) ),
    inference(instantiation,[status(thm)],[c_1682])).

cnf(c_3162,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2936])).

cnf(c_1688,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_3102,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1688])).

cnf(c_2919,plain,
    ( r1_tmap_1(sK2,sK0,X0_54,X1_54)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | X0_54 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | X1_54 != sK7 ),
    inference(instantiation,[status(thm)],[c_1700])).

cnf(c_3020,plain,
    ( r1_tmap_1(sK2,sK0,X0_54,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | X0_54 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2919])).

cnf(c_3101,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_3020])).

cnf(c_3096,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1689])).

cnf(c_1693,plain,
    ( ~ m1_subset_1(X0_54,X0_55)
    | m1_subset_1(X1_54,X1_55)
    | X1_55 != X0_55
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_2885,plain,
    ( m1_subset_1(X0_54,X0_55)
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | X0_55 != u1_struct_0(sK2)
    | X0_54 != sK7 ),
    inference(instantiation,[status(thm)],[c_1693])).

cnf(c_2975,plain,
    ( m1_subset_1(sK6,X0_55)
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | X0_55 != u1_struct_0(sK2)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2885])).

cnf(c_3095,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2975])).

cnf(c_2981,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1688])).

cnf(c_5,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1681,plain,
    ( ~ v3_pre_topc(X0_54,X0_53)
    | v3_pre_topc(X0_54,X1_53)
    | ~ m1_pre_topc(X1_53,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X1_53)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2914,plain,
    ( v3_pre_topc(sK5,X0_53)
    | ~ v3_pre_topc(sK5,sK1)
    | ~ m1_pre_topc(X0_53,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1681])).

cnf(c_2965,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ v3_pre_topc(sK5,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2914])).

cnf(c_2850,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1689])).

cnf(c_14,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1677,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2477,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1677])).

cnf(c_15,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1676,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2555,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2477,c_1676])).

cnf(c_2789,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK7)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2555])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1678,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2476,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1678])).

cnf(c_2560,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2476,c_1676])).

cnf(c_2786,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK7)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2560])).

cnf(c_1711,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1688])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_234,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_892,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | u1_struct_0(sK2) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_234,c_16])).

cnf(c_893,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_892])).

cnf(c_18,negated_conjecture,
    ( v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4909,c_4744,c_4525,c_4481,c_3813,c_3800,c_3302,c_3256,c_3162,c_3102,c_3101,c_3096,c_3095,c_2981,c_2965,c_2850,c_2789,c_2786,c_1676,c_1711,c_893,c_16,c_18,c_19,c_20,c_21,c_22,c_23,c_26,c_27,c_29,c_30,c_31,c_32,c_33,c_34,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.36/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/0.98  
% 2.36/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.36/0.98  
% 2.36/0.98  ------  iProver source info
% 2.36/0.98  
% 2.36/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.36/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.36/0.98  git: non_committed_changes: false
% 2.36/0.98  git: last_make_outside_of_git: false
% 2.36/0.98  
% 2.36/0.98  ------ 
% 2.36/0.98  
% 2.36/0.98  ------ Input Options
% 2.36/0.98  
% 2.36/0.98  --out_options                           all
% 2.36/0.98  --tptp_safe_out                         true
% 2.36/0.98  --problem_path                          ""
% 2.36/0.98  --include_path                          ""
% 2.36/0.98  --clausifier                            res/vclausify_rel
% 2.36/0.98  --clausifier_options                    --mode clausify
% 2.36/0.98  --stdin                                 false
% 2.36/0.98  --stats_out                             all
% 2.36/0.98  
% 2.36/0.98  ------ General Options
% 2.36/0.98  
% 2.36/0.98  --fof                                   false
% 2.36/0.98  --time_out_real                         305.
% 2.36/0.98  --time_out_virtual                      -1.
% 2.36/0.98  --symbol_type_check                     false
% 2.36/0.98  --clausify_out                          false
% 2.36/0.98  --sig_cnt_out                           false
% 2.36/0.98  --trig_cnt_out                          false
% 2.36/0.98  --trig_cnt_out_tolerance                1.
% 2.36/0.98  --trig_cnt_out_sk_spl                   false
% 2.36/0.98  --abstr_cl_out                          false
% 2.36/0.98  
% 2.36/0.98  ------ Global Options
% 2.36/0.98  
% 2.36/0.98  --schedule                              default
% 2.36/0.98  --add_important_lit                     false
% 2.36/0.98  --prop_solver_per_cl                    1000
% 2.36/0.98  --min_unsat_core                        false
% 2.36/0.98  --soft_assumptions                      false
% 2.36/0.98  --soft_lemma_size                       3
% 2.36/0.98  --prop_impl_unit_size                   0
% 2.36/0.98  --prop_impl_unit                        []
% 2.36/0.98  --share_sel_clauses                     true
% 2.36/0.98  --reset_solvers                         false
% 2.36/0.98  --bc_imp_inh                            [conj_cone]
% 2.36/0.98  --conj_cone_tolerance                   3.
% 2.36/0.98  --extra_neg_conj                        none
% 2.36/0.98  --large_theory_mode                     true
% 2.36/0.98  --prolific_symb_bound                   200
% 2.36/0.98  --lt_threshold                          2000
% 2.36/0.98  --clause_weak_htbl                      true
% 2.36/0.98  --gc_record_bc_elim                     false
% 2.36/0.98  
% 2.36/0.98  ------ Preprocessing Options
% 2.36/0.98  
% 2.36/0.98  --preprocessing_flag                    true
% 2.36/0.98  --time_out_prep_mult                    0.1
% 2.36/0.98  --splitting_mode                        input
% 2.36/0.98  --splitting_grd                         true
% 2.36/0.98  --splitting_cvd                         false
% 2.36/0.98  --splitting_cvd_svl                     false
% 2.36/0.98  --splitting_nvd                         32
% 2.36/0.98  --sub_typing                            true
% 2.36/0.98  --prep_gs_sim                           true
% 2.36/0.98  --prep_unflatten                        true
% 2.36/0.98  --prep_res_sim                          true
% 2.36/0.98  --prep_upred                            true
% 2.36/0.98  --prep_sem_filter                       exhaustive
% 2.36/0.98  --prep_sem_filter_out                   false
% 2.36/0.98  --pred_elim                             true
% 2.36/0.98  --res_sim_input                         true
% 2.36/0.98  --eq_ax_congr_red                       true
% 2.36/0.98  --pure_diseq_elim                       true
% 2.36/0.98  --brand_transform                       false
% 2.36/0.98  --non_eq_to_eq                          false
% 2.36/0.98  --prep_def_merge                        true
% 2.36/0.98  --prep_def_merge_prop_impl              false
% 2.36/0.98  --prep_def_merge_mbd                    true
% 2.36/0.98  --prep_def_merge_tr_red                 false
% 2.36/0.98  --prep_def_merge_tr_cl                  false
% 2.36/0.98  --smt_preprocessing                     true
% 2.36/0.98  --smt_ac_axioms                         fast
% 2.36/0.98  --preprocessed_out                      false
% 2.36/0.98  --preprocessed_stats                    false
% 2.36/0.98  
% 2.36/0.98  ------ Abstraction refinement Options
% 2.36/0.98  
% 2.36/0.98  --abstr_ref                             []
% 2.36/0.98  --abstr_ref_prep                        false
% 2.36/0.98  --abstr_ref_until_sat                   false
% 2.36/0.98  --abstr_ref_sig_restrict                funpre
% 2.36/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/0.98  --abstr_ref_under                       []
% 2.36/0.98  
% 2.36/0.98  ------ SAT Options
% 2.36/0.98  
% 2.36/0.98  --sat_mode                              false
% 2.36/0.98  --sat_fm_restart_options                ""
% 2.36/0.98  --sat_gr_def                            false
% 2.36/0.98  --sat_epr_types                         true
% 2.36/0.98  --sat_non_cyclic_types                  false
% 2.36/0.98  --sat_finite_models                     false
% 2.36/0.98  --sat_fm_lemmas                         false
% 2.36/0.98  --sat_fm_prep                           false
% 2.36/0.98  --sat_fm_uc_incr                        true
% 2.36/0.98  --sat_out_model                         small
% 2.36/0.98  --sat_out_clauses                       false
% 2.36/0.98  
% 2.36/0.98  ------ QBF Options
% 2.36/0.98  
% 2.36/0.98  --qbf_mode                              false
% 2.36/0.98  --qbf_elim_univ                         false
% 2.36/0.98  --qbf_dom_inst                          none
% 2.36/0.98  --qbf_dom_pre_inst                      false
% 2.36/0.98  --qbf_sk_in                             false
% 2.36/0.98  --qbf_pred_elim                         true
% 2.36/0.98  --qbf_split                             512
% 2.36/0.98  
% 2.36/0.98  ------ BMC1 Options
% 2.36/0.98  
% 2.36/0.98  --bmc1_incremental                      false
% 2.36/0.98  --bmc1_axioms                           reachable_all
% 2.36/0.98  --bmc1_min_bound                        0
% 2.36/0.98  --bmc1_max_bound                        -1
% 2.36/0.98  --bmc1_max_bound_default                -1
% 2.36/0.98  --bmc1_symbol_reachability              true
% 2.36/0.98  --bmc1_property_lemmas                  false
% 2.36/0.98  --bmc1_k_induction                      false
% 2.36/0.98  --bmc1_non_equiv_states                 false
% 2.36/0.98  --bmc1_deadlock                         false
% 2.36/0.98  --bmc1_ucm                              false
% 2.36/0.98  --bmc1_add_unsat_core                   none
% 2.36/0.98  --bmc1_unsat_core_children              false
% 2.36/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/0.98  --bmc1_out_stat                         full
% 2.36/0.98  --bmc1_ground_init                      false
% 2.36/0.98  --bmc1_pre_inst_next_state              false
% 2.36/0.98  --bmc1_pre_inst_state                   false
% 2.36/0.98  --bmc1_pre_inst_reach_state             false
% 2.36/0.98  --bmc1_out_unsat_core                   false
% 2.36/0.98  --bmc1_aig_witness_out                  false
% 2.36/0.98  --bmc1_verbose                          false
% 2.36/0.98  --bmc1_dump_clauses_tptp                false
% 2.36/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.36/0.98  --bmc1_dump_file                        -
% 2.36/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.36/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.36/0.98  --bmc1_ucm_extend_mode                  1
% 2.36/0.98  --bmc1_ucm_init_mode                    2
% 2.36/0.98  --bmc1_ucm_cone_mode                    none
% 2.36/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.36/0.98  --bmc1_ucm_relax_model                  4
% 2.36/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.36/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/0.98  --bmc1_ucm_layered_model                none
% 2.36/0.98  --bmc1_ucm_max_lemma_size               10
% 2.36/0.98  
% 2.36/0.98  ------ AIG Options
% 2.36/0.98  
% 2.36/0.98  --aig_mode                              false
% 2.36/0.98  
% 2.36/0.98  ------ Instantiation Options
% 2.36/0.98  
% 2.36/0.98  --instantiation_flag                    true
% 2.36/0.98  --inst_sos_flag                         false
% 2.36/0.98  --inst_sos_phase                        true
% 2.36/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/0.98  --inst_lit_sel_side                     num_symb
% 2.36/0.98  --inst_solver_per_active                1400
% 2.36/0.98  --inst_solver_calls_frac                1.
% 2.36/0.98  --inst_passive_queue_type               priority_queues
% 2.36/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/0.98  --inst_passive_queues_freq              [25;2]
% 2.36/0.98  --inst_dismatching                      true
% 2.36/0.98  --inst_eager_unprocessed_to_passive     true
% 2.36/0.98  --inst_prop_sim_given                   true
% 2.36/0.98  --inst_prop_sim_new                     false
% 2.36/0.98  --inst_subs_new                         false
% 2.36/0.98  --inst_eq_res_simp                      false
% 2.36/0.98  --inst_subs_given                       false
% 2.36/0.98  --inst_orphan_elimination               true
% 2.36/0.98  --inst_learning_loop_flag               true
% 2.36/0.98  --inst_learning_start                   3000
% 2.36/0.98  --inst_learning_factor                  2
% 2.36/0.98  --inst_start_prop_sim_after_learn       3
% 2.36/0.98  --inst_sel_renew                        solver
% 2.36/0.98  --inst_lit_activity_flag                true
% 2.36/0.98  --inst_restr_to_given                   false
% 2.36/0.98  --inst_activity_threshold               500
% 2.36/0.98  --inst_out_proof                        true
% 2.36/0.98  
% 2.36/0.98  ------ Resolution Options
% 2.36/0.98  
% 2.36/0.98  --resolution_flag                       true
% 2.36/0.98  --res_lit_sel                           adaptive
% 2.36/0.98  --res_lit_sel_side                      none
% 2.36/0.98  --res_ordering                          kbo
% 2.36/0.98  --res_to_prop_solver                    active
% 2.36/0.98  --res_prop_simpl_new                    false
% 2.36/0.98  --res_prop_simpl_given                  true
% 2.36/0.98  --res_passive_queue_type                priority_queues
% 2.36/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/0.98  --res_passive_queues_freq               [15;5]
% 2.36/0.98  --res_forward_subs                      full
% 2.36/0.98  --res_backward_subs                     full
% 2.36/0.98  --res_forward_subs_resolution           true
% 2.36/0.98  --res_backward_subs_resolution          true
% 2.36/0.98  --res_orphan_elimination                true
% 2.36/0.98  --res_time_limit                        2.
% 2.36/0.98  --res_out_proof                         true
% 2.36/0.98  
% 2.36/0.98  ------ Superposition Options
% 2.36/0.98  
% 2.36/0.98  --superposition_flag                    true
% 2.36/0.98  --sup_passive_queue_type                priority_queues
% 2.36/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.36/0.98  --demod_completeness_check              fast
% 2.36/0.98  --demod_use_ground                      true
% 2.36/0.98  --sup_to_prop_solver                    passive
% 2.36/0.98  --sup_prop_simpl_new                    true
% 2.36/0.98  --sup_prop_simpl_given                  true
% 2.36/0.98  --sup_fun_splitting                     false
% 2.36/0.98  --sup_smt_interval                      50000
% 2.36/0.98  
% 2.36/0.98  ------ Superposition Simplification Setup
% 2.36/0.98  
% 2.36/0.98  --sup_indices_passive                   []
% 2.36/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.98  --sup_full_bw                           [BwDemod]
% 2.36/0.98  --sup_immed_triv                        [TrivRules]
% 2.36/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.98  --sup_immed_bw_main                     []
% 2.36/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.98  
% 2.36/0.98  ------ Combination Options
% 2.36/0.98  
% 2.36/0.98  --comb_res_mult                         3
% 2.36/0.98  --comb_sup_mult                         2
% 2.36/0.98  --comb_inst_mult                        10
% 2.36/0.98  
% 2.36/0.98  ------ Debug Options
% 2.36/0.98  
% 2.36/0.98  --dbg_backtrace                         false
% 2.36/0.98  --dbg_dump_prop_clauses                 false
% 2.36/0.98  --dbg_dump_prop_clauses_file            -
% 2.36/0.98  --dbg_out_stat                          false
% 2.36/0.98  ------ Parsing...
% 2.36/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.36/0.98  
% 2.36/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.36/0.98  
% 2.36/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.36/0.98  
% 2.36/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.36/0.98  ------ Proving...
% 2.36/0.98  ------ Problem Properties 
% 2.36/0.98  
% 2.36/0.98  
% 2.36/0.98  clauses                                 33
% 2.36/0.98  conjectures                             20
% 2.36/0.98  EPR                                     17
% 2.36/0.98  Horn                                    27
% 2.36/0.98  unary                                   18
% 2.36/0.98  binary                                  5
% 2.36/0.98  lits                                    128
% 2.36/0.98  lits eq                                 13
% 2.36/0.98  fd_pure                                 0
% 2.36/0.98  fd_pseudo                               0
% 2.36/0.98  fd_cond                                 0
% 2.36/0.98  fd_pseudo_cond                          0
% 2.36/0.98  AC symbols                              0
% 2.36/0.98  
% 2.36/0.98  ------ Schedule dynamic 5 is on 
% 2.36/0.98  
% 2.36/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.36/0.98  
% 2.36/0.98  
% 2.36/0.98  ------ 
% 2.36/0.98  Current options:
% 2.36/0.98  ------ 
% 2.36/0.98  
% 2.36/0.98  ------ Input Options
% 2.36/0.98  
% 2.36/0.98  --out_options                           all
% 2.36/0.98  --tptp_safe_out                         true
% 2.36/0.98  --problem_path                          ""
% 2.36/0.98  --include_path                          ""
% 2.36/0.98  --clausifier                            res/vclausify_rel
% 2.36/0.98  --clausifier_options                    --mode clausify
% 2.36/0.98  --stdin                                 false
% 2.36/0.98  --stats_out                             all
% 2.36/0.98  
% 2.36/0.98  ------ General Options
% 2.36/0.98  
% 2.36/0.98  --fof                                   false
% 2.36/0.98  --time_out_real                         305.
% 2.36/0.98  --time_out_virtual                      -1.
% 2.36/0.98  --symbol_type_check                     false
% 2.36/0.98  --clausify_out                          false
% 2.36/0.98  --sig_cnt_out                           false
% 2.36/0.98  --trig_cnt_out                          false
% 2.36/0.98  --trig_cnt_out_tolerance                1.
% 2.36/0.98  --trig_cnt_out_sk_spl                   false
% 2.36/0.98  --abstr_cl_out                          false
% 2.36/0.98  
% 2.36/0.98  ------ Global Options
% 2.36/0.98  
% 2.36/0.98  --schedule                              default
% 2.36/0.98  --add_important_lit                     false
% 2.36/0.98  --prop_solver_per_cl                    1000
% 2.36/0.98  --min_unsat_core                        false
% 2.36/0.98  --soft_assumptions                      false
% 2.36/0.98  --soft_lemma_size                       3
% 2.36/0.98  --prop_impl_unit_size                   0
% 2.36/0.98  --prop_impl_unit                        []
% 2.36/0.98  --share_sel_clauses                     true
% 2.36/0.98  --reset_solvers                         false
% 2.36/0.98  --bc_imp_inh                            [conj_cone]
% 2.36/0.98  --conj_cone_tolerance                   3.
% 2.36/0.98  --extra_neg_conj                        none
% 2.36/0.98  --large_theory_mode                     true
% 2.36/0.98  --prolific_symb_bound                   200
% 2.36/0.98  --lt_threshold                          2000
% 2.36/0.98  --clause_weak_htbl                      true
% 2.36/0.98  --gc_record_bc_elim                     false
% 2.36/0.98  
% 2.36/0.98  ------ Preprocessing Options
% 2.36/0.98  
% 2.36/0.98  --preprocessing_flag                    true
% 2.36/0.98  --time_out_prep_mult                    0.1
% 2.36/0.98  --splitting_mode                        input
% 2.36/0.98  --splitting_grd                         true
% 2.36/0.98  --splitting_cvd                         false
% 2.36/0.98  --splitting_cvd_svl                     false
% 2.36/0.98  --splitting_nvd                         32
% 2.36/0.98  --sub_typing                            true
% 2.36/0.98  --prep_gs_sim                           true
% 2.36/0.98  --prep_unflatten                        true
% 2.36/0.98  --prep_res_sim                          true
% 2.36/0.98  --prep_upred                            true
% 2.36/0.98  --prep_sem_filter                       exhaustive
% 2.36/0.98  --prep_sem_filter_out                   false
% 2.36/0.98  --pred_elim                             true
% 2.36/0.98  --res_sim_input                         true
% 2.36/0.98  --eq_ax_congr_red                       true
% 2.36/0.98  --pure_diseq_elim                       true
% 2.36/0.98  --brand_transform                       false
% 2.36/0.98  --non_eq_to_eq                          false
% 2.36/0.98  --prep_def_merge                        true
% 2.36/0.98  --prep_def_merge_prop_impl              false
% 2.36/0.98  --prep_def_merge_mbd                    true
% 2.36/0.98  --prep_def_merge_tr_red                 false
% 2.36/0.98  --prep_def_merge_tr_cl                  false
% 2.36/0.98  --smt_preprocessing                     true
% 2.36/0.98  --smt_ac_axioms                         fast
% 2.36/0.98  --preprocessed_out                      false
% 2.36/0.98  --preprocessed_stats                    false
% 2.36/0.98  
% 2.36/0.98  ------ Abstraction refinement Options
% 2.36/0.98  
% 2.36/0.98  --abstr_ref                             []
% 2.36/0.98  --abstr_ref_prep                        false
% 2.36/0.98  --abstr_ref_until_sat                   false
% 2.36/0.98  --abstr_ref_sig_restrict                funpre
% 2.36/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/0.98  --abstr_ref_under                       []
% 2.36/0.98  
% 2.36/0.98  ------ SAT Options
% 2.36/0.98  
% 2.36/0.98  --sat_mode                              false
% 2.36/0.98  --sat_fm_restart_options                ""
% 2.36/0.98  --sat_gr_def                            false
% 2.36/0.98  --sat_epr_types                         true
% 2.36/0.98  --sat_non_cyclic_types                  false
% 2.36/0.98  --sat_finite_models                     false
% 2.36/0.98  --sat_fm_lemmas                         false
% 2.36/0.98  --sat_fm_prep                           false
% 2.36/0.98  --sat_fm_uc_incr                        true
% 2.36/0.98  --sat_out_model                         small
% 2.36/0.98  --sat_out_clauses                       false
% 2.36/0.98  
% 2.36/0.98  ------ QBF Options
% 2.36/0.98  
% 2.36/0.98  --qbf_mode                              false
% 2.36/0.98  --qbf_elim_univ                         false
% 2.36/0.98  --qbf_dom_inst                          none
% 2.36/0.98  --qbf_dom_pre_inst                      false
% 2.36/0.98  --qbf_sk_in                             false
% 2.36/0.98  --qbf_pred_elim                         true
% 2.36/0.98  --qbf_split                             512
% 2.36/0.98  
% 2.36/0.98  ------ BMC1 Options
% 2.36/0.98  
% 2.36/0.98  --bmc1_incremental                      false
% 2.36/0.98  --bmc1_axioms                           reachable_all
% 2.36/0.98  --bmc1_min_bound                        0
% 2.36/0.98  --bmc1_max_bound                        -1
% 2.36/0.98  --bmc1_max_bound_default                -1
% 2.36/0.98  --bmc1_symbol_reachability              true
% 2.36/0.98  --bmc1_property_lemmas                  false
% 2.36/0.98  --bmc1_k_induction                      false
% 2.36/0.98  --bmc1_non_equiv_states                 false
% 2.36/0.98  --bmc1_deadlock                         false
% 2.36/0.98  --bmc1_ucm                              false
% 2.36/0.98  --bmc1_add_unsat_core                   none
% 2.36/0.98  --bmc1_unsat_core_children              false
% 2.36/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/0.98  --bmc1_out_stat                         full
% 2.36/0.98  --bmc1_ground_init                      false
% 2.36/0.98  --bmc1_pre_inst_next_state              false
% 2.36/0.98  --bmc1_pre_inst_state                   false
% 2.36/0.98  --bmc1_pre_inst_reach_state             false
% 2.36/0.98  --bmc1_out_unsat_core                   false
% 2.36/0.98  --bmc1_aig_witness_out                  false
% 2.36/0.98  --bmc1_verbose                          false
% 2.36/0.98  --bmc1_dump_clauses_tptp                false
% 2.36/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.36/0.98  --bmc1_dump_file                        -
% 2.36/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.36/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.36/0.98  --bmc1_ucm_extend_mode                  1
% 2.36/0.98  --bmc1_ucm_init_mode                    2
% 2.36/0.98  --bmc1_ucm_cone_mode                    none
% 2.36/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.36/0.98  --bmc1_ucm_relax_model                  4
% 2.36/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.36/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/0.98  --bmc1_ucm_layered_model                none
% 2.36/0.98  --bmc1_ucm_max_lemma_size               10
% 2.36/0.98  
% 2.36/0.98  ------ AIG Options
% 2.36/0.98  
% 2.36/0.98  --aig_mode                              false
% 2.36/0.98  
% 2.36/0.98  ------ Instantiation Options
% 2.36/0.98  
% 2.36/0.98  --instantiation_flag                    true
% 2.36/0.98  --inst_sos_flag                         false
% 2.36/0.98  --inst_sos_phase                        true
% 2.36/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/0.98  --inst_lit_sel_side                     none
% 2.36/0.98  --inst_solver_per_active                1400
% 2.36/0.98  --inst_solver_calls_frac                1.
% 2.36/0.98  --inst_passive_queue_type               priority_queues
% 2.36/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/0.98  --inst_passive_queues_freq              [25;2]
% 2.36/0.98  --inst_dismatching                      true
% 2.36/0.98  --inst_eager_unprocessed_to_passive     true
% 2.36/0.98  --inst_prop_sim_given                   true
% 2.36/0.98  --inst_prop_sim_new                     false
% 2.36/0.98  --inst_subs_new                         false
% 2.36/0.98  --inst_eq_res_simp                      false
% 2.36/0.98  --inst_subs_given                       false
% 2.36/0.98  --inst_orphan_elimination               true
% 2.36/0.98  --inst_learning_loop_flag               true
% 2.36/0.98  --inst_learning_start                   3000
% 2.36/0.98  --inst_learning_factor                  2
% 2.36/0.98  --inst_start_prop_sim_after_learn       3
% 2.36/0.98  --inst_sel_renew                        solver
% 2.36/0.98  --inst_lit_activity_flag                true
% 2.36/0.98  --inst_restr_to_given                   false
% 2.36/0.98  --inst_activity_threshold               500
% 2.36/0.98  --inst_out_proof                        true
% 2.36/0.98  
% 2.36/0.98  ------ Resolution Options
% 2.36/0.98  
% 2.36/0.98  --resolution_flag                       false
% 2.36/0.98  --res_lit_sel                           adaptive
% 2.36/0.98  --res_lit_sel_side                      none
% 2.36/0.98  --res_ordering                          kbo
% 2.36/0.98  --res_to_prop_solver                    active
% 2.36/0.98  --res_prop_simpl_new                    false
% 2.36/0.98  --res_prop_simpl_given                  true
% 2.36/0.98  --res_passive_queue_type                priority_queues
% 2.36/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/0.98  --res_passive_queues_freq               [15;5]
% 2.36/0.98  --res_forward_subs                      full
% 2.36/0.98  --res_backward_subs                     full
% 2.36/0.98  --res_forward_subs_resolution           true
% 2.36/0.98  --res_backward_subs_resolution          true
% 2.36/0.98  --res_orphan_elimination                true
% 2.36/0.98  --res_time_limit                        2.
% 2.36/0.98  --res_out_proof                         true
% 2.36/0.98  
% 2.36/0.98  ------ Superposition Options
% 2.36/0.98  
% 2.36/0.98  --superposition_flag                    true
% 2.36/0.98  --sup_passive_queue_type                priority_queues
% 2.36/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.36/0.98  --demod_completeness_check              fast
% 2.36/0.98  --demod_use_ground                      true
% 2.36/0.98  --sup_to_prop_solver                    passive
% 2.36/0.98  --sup_prop_simpl_new                    true
% 2.36/0.98  --sup_prop_simpl_given                  true
% 2.36/0.98  --sup_fun_splitting                     false
% 2.36/0.98  --sup_smt_interval                      50000
% 2.36/0.98  
% 2.36/0.98  ------ Superposition Simplification Setup
% 2.36/0.98  
% 2.36/0.98  --sup_indices_passive                   []
% 2.36/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.98  --sup_full_bw                           [BwDemod]
% 2.36/0.98  --sup_immed_triv                        [TrivRules]
% 2.36/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.98  --sup_immed_bw_main                     []
% 2.36/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.98  
% 2.36/0.98  ------ Combination Options
% 2.36/0.98  
% 2.36/0.98  --comb_res_mult                         3
% 2.36/0.98  --comb_sup_mult                         2
% 2.36/0.98  --comb_inst_mult                        10
% 2.36/0.98  
% 2.36/0.98  ------ Debug Options
% 2.36/0.98  
% 2.36/0.98  --dbg_backtrace                         false
% 2.36/0.98  --dbg_dump_prop_clauses                 false
% 2.36/0.98  --dbg_dump_prop_clauses_file            -
% 2.36/0.98  --dbg_out_stat                          false
% 2.36/0.98  
% 2.36/0.98  
% 2.36/0.98  
% 2.36/0.98  
% 2.36/0.98  ------ Proving...
% 2.36/0.98  
% 2.36/0.98  
% 2.36/0.98  % SZS status Theorem for theBenchmark.p
% 2.36/0.98  
% 2.36/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.36/0.98  
% 2.36/0.98  fof(f11,axiom,(
% 2.36/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f29,plain,(
% 2.36/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.36/0.98    inference(ennf_transformation,[],[f11])).
% 2.36/0.98  
% 2.36/0.98  fof(f30,plain,(
% 2.36/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.36/0.98    inference(flattening,[],[f29])).
% 2.36/0.98  
% 2.36/0.98  fof(f34,plain,(
% 2.36/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.36/0.98    inference(nnf_transformation,[],[f30])).
% 2.36/0.98  
% 2.36/0.98  fof(f57,plain,(
% 2.36/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.36/0.98    inference(cnf_transformation,[],[f34])).
% 2.36/0.98  
% 2.36/0.98  fof(f85,plain,(
% 2.36/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.36/0.98    inference(equality_resolution,[],[f57])).
% 2.36/0.98  
% 2.36/0.98  fof(f12,conjecture,(
% 2.36/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 2.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f13,negated_conjecture,(
% 2.36/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 2.36/0.98    inference(negated_conjecture,[],[f12])).
% 2.36/0.98  
% 2.36/0.98  fof(f31,plain,(
% 2.36/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.36/0.98    inference(ennf_transformation,[],[f13])).
% 2.36/0.98  
% 2.36/0.98  fof(f32,plain,(
% 2.36/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.36/0.98    inference(flattening,[],[f31])).
% 2.36/0.98  
% 2.36/0.98  fof(f35,plain,(
% 2.36/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.36/0.98    inference(nnf_transformation,[],[f32])).
% 2.36/0.98  
% 2.36/0.98  fof(f36,plain,(
% 2.36/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.36/0.98    inference(flattening,[],[f35])).
% 2.36/0.98  
% 2.36/0.98  fof(f44,plain,(
% 2.36/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | r1_tmap_1(X3,X0,X4,X6)) & sK7 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 2.36/0.98    introduced(choice_axiom,[])).
% 2.36/0.98  
% 2.36/0.98  fof(f43,plain,(
% 2.36/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,sK6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,sK6)) & sK6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.36/0.98    introduced(choice_axiom,[])).
% 2.36/0.98  
% 2.36/0.98  fof(f42,plain,(
% 2.36/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(X2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 2.36/0.98    introduced(choice_axiom,[])).
% 2.36/0.98  
% 2.36/0.98  fof(f41,plain,(
% 2.36/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7) | ~r1_tmap_1(X3,X0,sK4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7) | r1_tmap_1(X3,X0,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 2.36/0.98    introduced(choice_axiom,[])).
% 2.36/0.98  
% 2.36/0.98  fof(f40,plain,(
% 2.36/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7) | ~r1_tmap_1(sK3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7) | r1_tmap_1(sK3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 2.36/0.98    introduced(choice_axiom,[])).
% 2.36/0.98  
% 2.36/0.98  fof(f39,plain,(
% 2.36/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 2.36/0.98    introduced(choice_axiom,[])).
% 2.36/0.98  
% 2.36/0.98  fof(f38,plain,(
% 2.36/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.36/0.98    introduced(choice_axiom,[])).
% 2.36/0.98  
% 2.36/0.98  fof(f37,plain,(
% 2.36/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.36/0.98    introduced(choice_axiom,[])).
% 2.36/0.98  
% 2.36/0.98  fof(f45,plain,(
% 2.36/0.98    ((((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.36/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f36,f44,f43,f42,f41,f40,f39,f38,f37])).
% 2.36/0.98  
% 2.36/0.98  fof(f77,plain,(
% 2.36/0.98    r2_hidden(sK6,sK5)),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f10,axiom,(
% 2.36/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f27,plain,(
% 2.36/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.36/0.98    inference(ennf_transformation,[],[f10])).
% 2.36/0.98  
% 2.36/0.98  fof(f28,plain,(
% 2.36/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.36/0.98    inference(flattening,[],[f27])).
% 2.36/0.98  
% 2.36/0.98  fof(f56,plain,(
% 2.36/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.36/0.98    inference(cnf_transformation,[],[f28])).
% 2.36/0.98  
% 2.36/0.98  fof(f70,plain,(
% 2.36/0.98    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f69,plain,(
% 2.36/0.98    v1_funct_1(sK4)),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f58,plain,(
% 2.36/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.36/0.98    inference(cnf_transformation,[],[f34])).
% 2.36/0.98  
% 2.36/0.98  fof(f84,plain,(
% 2.36/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.36/0.98    inference(equality_resolution,[],[f58])).
% 2.36/0.98  
% 2.36/0.98  fof(f3,axiom,(
% 2.36/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f16,plain,(
% 2.36/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.36/0.98    inference(ennf_transformation,[],[f3])).
% 2.36/0.98  
% 2.36/0.98  fof(f49,plain,(
% 2.36/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.36/0.98    inference(cnf_transformation,[],[f16])).
% 2.36/0.98  
% 2.36/0.98  fof(f4,axiom,(
% 2.36/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f17,plain,(
% 2.36/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.36/0.98    inference(ennf_transformation,[],[f4])).
% 2.36/0.98  
% 2.36/0.98  fof(f50,plain,(
% 2.36/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.36/0.98    inference(cnf_transformation,[],[f17])).
% 2.36/0.98  
% 2.36/0.98  fof(f5,axiom,(
% 2.36/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 2.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f18,plain,(
% 2.36/0.98    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.36/0.98    inference(ennf_transformation,[],[f5])).
% 2.36/0.98  
% 2.36/0.98  fof(f19,plain,(
% 2.36/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.36/0.98    inference(flattening,[],[f18])).
% 2.36/0.98  
% 2.36/0.98  fof(f51,plain,(
% 2.36/0.98    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.36/0.98    inference(cnf_transformation,[],[f19])).
% 2.36/0.98  
% 2.36/0.98  fof(f82,plain,(
% 2.36/0.98    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.36/0.98    inference(equality_resolution,[],[f51])).
% 2.36/0.98  
% 2.36/0.98  fof(f80,plain,(
% 2.36/0.98    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f79,plain,(
% 2.36/0.98    sK6 = sK7),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f81,plain,(
% 2.36/0.98    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f1,axiom,(
% 2.36/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.98  
% 2.36/0.98  fof(f33,plain,(
% 2.36/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.36/0.98    inference(nnf_transformation,[],[f1])).
% 2.36/0.98  
% 2.36/0.98  fof(f47,plain,(
% 2.36/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.36/0.98    inference(cnf_transformation,[],[f33])).
% 2.36/0.98  
% 2.36/0.98  fof(f78,plain,(
% 2.36/0.98    r1_tarski(sK5,u1_struct_0(sK2))),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f76,plain,(
% 2.36/0.98    v3_pre_topc(sK5,sK1)),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f75,plain,(
% 2.36/0.98    m1_subset_1(sK7,u1_struct_0(sK2))),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f74,plain,(
% 2.36/0.98    m1_subset_1(sK6,u1_struct_0(sK3))),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f73,plain,(
% 2.36/0.98    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f72,plain,(
% 2.36/0.98    m1_pre_topc(sK2,sK3)),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f71,plain,(
% 2.36/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f68,plain,(
% 2.36/0.98    m1_pre_topc(sK3,sK1)),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f67,plain,(
% 2.36/0.98    ~v2_struct_0(sK3)),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f65,plain,(
% 2.36/0.98    ~v2_struct_0(sK2)),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f64,plain,(
% 2.36/0.98    l1_pre_topc(sK1)),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f63,plain,(
% 2.36/0.98    v2_pre_topc(sK1)),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f62,plain,(
% 2.36/0.98    ~v2_struct_0(sK1)),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f61,plain,(
% 2.36/0.98    l1_pre_topc(sK0)),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f60,plain,(
% 2.36/0.98    v2_pre_topc(sK0)),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  fof(f59,plain,(
% 2.36/0.98    ~v2_struct_0(sK0)),
% 2.36/0.98    inference(cnf_transformation,[],[f45])).
% 2.36/0.98  
% 2.36/0.98  cnf(c_12,plain,
% 2.36/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.36/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.36/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.36/0.98      | ~ r2_hidden(X3,X6)
% 2.36/0.98      | ~ v3_pre_topc(X6,X0)
% 2.36/0.98      | ~ m1_pre_topc(X4,X5)
% 2.36/0.98      | ~ m1_pre_topc(X0,X5)
% 2.36/0.98      | ~ m1_pre_topc(X4,X0)
% 2.36/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.36/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.36/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.36/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.36/0.98      | v2_struct_0(X5)
% 2.36/0.98      | v2_struct_0(X1)
% 2.36/0.98      | v2_struct_0(X4)
% 2.36/0.98      | v2_struct_0(X0)
% 2.36/0.98      | ~ v1_funct_1(X2)
% 2.36/0.98      | ~ l1_pre_topc(X5)
% 2.36/0.98      | ~ l1_pre_topc(X1)
% 2.36/0.98      | ~ v2_pre_topc(X5)
% 2.36/0.98      | ~ v2_pre_topc(X1) ),
% 2.36/0.98      inference(cnf_transformation,[],[f85]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_17,negated_conjecture,
% 2.36/0.98      ( r2_hidden(sK6,sK5) ),
% 2.36/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_452,plain,
% 2.36/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.36/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.36/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.36/0.98      | ~ v3_pre_topc(X6,X0)
% 2.36/0.98      | ~ m1_pre_topc(X4,X0)
% 2.36/0.98      | ~ m1_pre_topc(X4,X5)
% 2.36/0.98      | ~ m1_pre_topc(X0,X5)
% 2.36/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.36/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.36/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.36/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.36/0.98      | v2_struct_0(X0)
% 2.36/0.98      | v2_struct_0(X1)
% 2.36/0.98      | v2_struct_0(X4)
% 2.36/0.98      | v2_struct_0(X5)
% 2.36/0.98      | ~ v1_funct_1(X2)
% 2.36/0.98      | ~ l1_pre_topc(X1)
% 2.36/0.98      | ~ l1_pre_topc(X5)
% 2.36/0.98      | ~ v2_pre_topc(X1)
% 2.36/0.98      | ~ v2_pre_topc(X5)
% 2.36/0.98      | sK5 != X6
% 2.36/0.98      | sK6 != X3 ),
% 2.36/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_453,plain,
% 2.36/0.98      ( ~ r1_tmap_1(X0,X1,X2,sK6)
% 2.36/0.98      | r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
% 2.36/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.36/0.98      | ~ v3_pre_topc(sK5,X0)
% 2.36/0.98      | ~ m1_pre_topc(X3,X0)
% 2.36/0.98      | ~ m1_pre_topc(X3,X4)
% 2.36/0.98      | ~ m1_pre_topc(X0,X4)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 2.36/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.36/0.98      | v2_struct_0(X0)
% 2.36/0.98      | v2_struct_0(X1)
% 2.36/0.98      | v2_struct_0(X3)
% 2.36/0.98      | v2_struct_0(X4)
% 2.36/0.98      | ~ v1_funct_1(X2)
% 2.36/0.98      | ~ l1_pre_topc(X1)
% 2.36/0.98      | ~ l1_pre_topc(X4)
% 2.36/0.98      | ~ v2_pre_topc(X1)
% 2.36/0.98      | ~ v2_pre_topc(X4) ),
% 2.36/0.98      inference(unflattening,[status(thm)],[c_452]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_10,plain,
% 2.36/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.36/0.98      | ~ m1_pre_topc(X2,X0)
% 2.36/0.98      | m1_pre_topc(X2,X1)
% 2.36/0.98      | ~ l1_pre_topc(X1)
% 2.36/0.98      | ~ v2_pre_topc(X1) ),
% 2.36/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_499,plain,
% 2.36/0.98      ( ~ r1_tmap_1(X0,X1,X2,sK6)
% 2.36/0.98      | r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
% 2.36/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.36/0.98      | ~ v3_pre_topc(sK5,X0)
% 2.36/0.98      | ~ m1_pre_topc(X3,X0)
% 2.36/0.98      | ~ m1_pre_topc(X0,X4)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 2.36/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.36/0.98      | v2_struct_0(X0)
% 2.36/0.98      | v2_struct_0(X1)
% 2.36/0.98      | v2_struct_0(X3)
% 2.36/0.98      | v2_struct_0(X4)
% 2.36/0.98      | ~ v1_funct_1(X2)
% 2.36/0.98      | ~ l1_pre_topc(X1)
% 2.36/0.98      | ~ l1_pre_topc(X4)
% 2.36/0.98      | ~ v2_pre_topc(X1)
% 2.36/0.98      | ~ v2_pre_topc(X4) ),
% 2.36/0.98      inference(forward_subsumption_resolution,
% 2.36/0.98                [status(thm)],
% 2.36/0.98                [c_453,c_10]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_24,negated_conjecture,
% 2.36/0.98      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
% 2.36/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_664,plain,
% 2.36/0.98      ( ~ r1_tmap_1(X0,X1,X2,sK6)
% 2.36/0.98      | r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
% 2.36/0.98      | ~ v3_pre_topc(sK5,X0)
% 2.36/0.98      | ~ m1_pre_topc(X3,X0)
% 2.36/0.98      | ~ m1_pre_topc(X0,X4)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 2.36/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.36/0.98      | v2_struct_0(X0)
% 2.36/0.98      | v2_struct_0(X1)
% 2.36/0.98      | v2_struct_0(X3)
% 2.36/0.98      | v2_struct_0(X4)
% 2.36/0.98      | ~ v1_funct_1(X2)
% 2.36/0.98      | ~ l1_pre_topc(X1)
% 2.36/0.98      | ~ l1_pre_topc(X4)
% 2.36/0.98      | ~ v2_pre_topc(X1)
% 2.36/0.98      | ~ v2_pre_topc(X4)
% 2.36/0.98      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.36/0.98      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.36/0.98      | sK4 != X2 ),
% 2.36/0.98      inference(resolution_lifted,[status(thm)],[c_499,c_24]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_665,plain,
% 2.36/0.98      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 2.36/0.98      | ~ r1_tmap_1(X3,X1,sK4,sK6)
% 2.36/0.98      | ~ v3_pre_topc(sK5,X3)
% 2.36/0.98      | ~ m1_pre_topc(X0,X3)
% 2.36/0.98      | ~ m1_pre_topc(X3,X2)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.36/0.98      | v2_struct_0(X3)
% 2.36/0.98      | v2_struct_0(X1)
% 2.36/0.98      | v2_struct_0(X0)
% 2.36/0.98      | v2_struct_0(X2)
% 2.36/0.98      | ~ v1_funct_1(sK4)
% 2.36/0.98      | ~ l1_pre_topc(X1)
% 2.36/0.98      | ~ l1_pre_topc(X2)
% 2.36/0.98      | ~ v2_pre_topc(X1)
% 2.36/0.98      | ~ v2_pre_topc(X2)
% 2.36/0.98      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.36/0.98      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.36/0.98      inference(unflattening,[status(thm)],[c_664]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_25,negated_conjecture,
% 2.36/0.98      ( v1_funct_1(sK4) ),
% 2.36/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_669,plain,
% 2.36/0.98      ( v2_struct_0(X2)
% 2.36/0.98      | v2_struct_0(X0)
% 2.36/0.98      | v2_struct_0(X1)
% 2.36/0.98      | v2_struct_0(X3)
% 2.36/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_pre_topc(X3,X2)
% 2.36/0.98      | ~ m1_pre_topc(X0,X3)
% 2.36/0.98      | ~ v3_pre_topc(sK5,X3)
% 2.36/0.98      | ~ r1_tmap_1(X3,X1,sK4,sK6)
% 2.36/0.98      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 2.36/0.98      | ~ l1_pre_topc(X1)
% 2.36/0.98      | ~ l1_pre_topc(X2)
% 2.36/0.98      | ~ v2_pre_topc(X1)
% 2.36/0.98      | ~ v2_pre_topc(X2)
% 2.36/0.98      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.36/0.98      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.36/0.98      inference(global_propositional_subsumption,
% 2.36/0.98                [status(thm)],
% 2.36/0.98                [c_665,c_25]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_670,plain,
% 2.36/0.98      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 2.36/0.98      | ~ r1_tmap_1(X3,X1,sK4,sK6)
% 2.36/0.98      | ~ v3_pre_topc(sK5,X3)
% 2.36/0.98      | ~ m1_pre_topc(X3,X2)
% 2.36/0.98      | ~ m1_pre_topc(X0,X3)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.36/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.36/0.98      | v2_struct_0(X0)
% 2.36/0.98      | v2_struct_0(X1)
% 2.36/0.98      | v2_struct_0(X2)
% 2.36/0.98      | v2_struct_0(X3)
% 2.36/0.98      | ~ l1_pre_topc(X1)
% 2.36/0.98      | ~ l1_pre_topc(X2)
% 2.36/0.98      | ~ v2_pre_topc(X1)
% 2.36/0.98      | ~ v2_pre_topc(X2)
% 2.36/0.98      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.36/0.98      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.36/0.98      inference(renaming,[status(thm)],[c_669]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1657,plain,
% 2.36/0.98      ( r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),sK6)
% 2.36/0.98      | ~ r1_tmap_1(X3_53,X1_53,sK4,sK6)
% 2.36/0.98      | ~ v3_pre_topc(sK5,X3_53)
% 2.36/0.98      | ~ m1_pre_topc(X3_53,X2_53)
% 2.36/0.98      | ~ m1_pre_topc(X0_53,X3_53)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(X0_53))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_53)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X3_53))
% 2.36/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
% 2.36/0.98      | v2_struct_0(X1_53)
% 2.36/0.98      | v2_struct_0(X2_53)
% 2.36/0.98      | v2_struct_0(X3_53)
% 2.36/0.98      | v2_struct_0(X0_53)
% 2.36/0.98      | ~ l1_pre_topc(X1_53)
% 2.36/0.98      | ~ l1_pre_topc(X2_53)
% 2.36/0.98      | ~ v2_pre_topc(X1_53)
% 2.36/0.98      | ~ v2_pre_topc(X2_53)
% 2.36/0.98      | u1_struct_0(X3_53) != u1_struct_0(sK3)
% 2.36/0.98      | u1_struct_0(X1_53) != u1_struct_0(sK0) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_670]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3052,plain,
% 2.36/0.98      ( r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,sK3,X0_53,sK4),sK6)
% 2.36/0.98      | ~ r1_tmap_1(sK3,X1_53,sK4,sK6)
% 2.36/0.98      | ~ v3_pre_topc(sK5,sK3)
% 2.36/0.98      | ~ m1_pre_topc(X0_53,sK3)
% 2.36/0.98      | ~ m1_pre_topc(sK3,X2_53)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(X0_53))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.36/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
% 2.36/0.98      | v2_struct_0(X1_53)
% 2.36/0.98      | v2_struct_0(X2_53)
% 2.36/0.98      | v2_struct_0(X0_53)
% 2.36/0.98      | v2_struct_0(sK3)
% 2.36/0.98      | ~ l1_pre_topc(X1_53)
% 2.36/0.98      | ~ l1_pre_topc(X2_53)
% 2.36/0.98      | ~ v2_pre_topc(X1_53)
% 2.36/0.98      | ~ v2_pre_topc(X2_53)
% 2.36/0.98      | u1_struct_0(X1_53) != u1_struct_0(sK0)
% 2.36/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1657]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3405,plain,
% 2.36/0.98      ( ~ r1_tmap_1(sK3,X0_53,sK4,sK6)
% 2.36/0.98      | r1_tmap_1(sK2,X0_53,k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4),sK6)
% 2.36/0.98      | ~ v3_pre_topc(sK5,sK3)
% 2.36/0.98      | ~ m1_pre_topc(sK3,X1_53)
% 2.36/0.98      | ~ m1_pre_topc(sK2,sK3)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 2.36/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 2.36/0.98      | v2_struct_0(X1_53)
% 2.36/0.98      | v2_struct_0(X0_53)
% 2.36/0.98      | v2_struct_0(sK3)
% 2.36/0.98      | v2_struct_0(sK2)
% 2.36/0.98      | ~ l1_pre_topc(X1_53)
% 2.36/0.98      | ~ l1_pre_topc(X0_53)
% 2.36/0.98      | ~ v2_pre_topc(X1_53)
% 2.36/0.98      | ~ v2_pre_topc(X0_53)
% 2.36/0.98      | u1_struct_0(X0_53) != u1_struct_0(sK0)
% 2.36/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_3052]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_4907,plain,
% 2.36/0.98      ( ~ r1_tmap_1(sK3,X0_53,sK4,sK6)
% 2.36/0.98      | r1_tmap_1(sK2,X0_53,k3_tmap_1(sK1,X0_53,sK3,sK2,sK4),sK6)
% 2.36/0.98      | ~ v3_pre_topc(sK5,sK3)
% 2.36/0.98      | ~ m1_pre_topc(sK3,sK1)
% 2.36/0.98      | ~ m1_pre_topc(sK2,sK3)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 2.36/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 2.36/0.98      | v2_struct_0(X0_53)
% 2.36/0.98      | v2_struct_0(sK3)
% 2.36/0.98      | v2_struct_0(sK1)
% 2.36/0.98      | v2_struct_0(sK2)
% 2.36/0.98      | ~ l1_pre_topc(X0_53)
% 2.36/0.98      | ~ l1_pre_topc(sK1)
% 2.36/0.98      | ~ v2_pre_topc(X0_53)
% 2.36/0.98      | ~ v2_pre_topc(sK1)
% 2.36/0.98      | u1_struct_0(X0_53) != u1_struct_0(sK0)
% 2.36/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_3405]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_4909,plain,
% 2.36/0.98      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.36/0.98      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 2.36/0.98      | ~ v3_pre_topc(sK5,sK3)
% 2.36/0.98      | ~ m1_pre_topc(sK3,sK1)
% 2.36/0.98      | ~ m1_pre_topc(sK2,sK3)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 2.36/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
% 2.36/0.98      | v2_struct_0(sK3)
% 2.36/0.98      | v2_struct_0(sK1)
% 2.36/0.98      | v2_struct_0(sK0)
% 2.36/0.98      | v2_struct_0(sK2)
% 2.36/0.98      | ~ l1_pre_topc(sK1)
% 2.36/0.98      | ~ l1_pre_topc(sK0)
% 2.36/0.98      | ~ v2_pre_topc(sK1)
% 2.36/0.98      | ~ v2_pre_topc(sK0)
% 2.36/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.36/0.98      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_4907]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_11,plain,
% 2.36/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 2.36/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.36/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.36/0.98      | ~ r2_hidden(X3,X6)
% 2.36/0.98      | ~ v3_pre_topc(X6,X0)
% 2.36/0.98      | ~ m1_pre_topc(X4,X5)
% 2.36/0.98      | ~ m1_pre_topc(X0,X5)
% 2.36/0.98      | ~ m1_pre_topc(X4,X0)
% 2.36/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.36/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.36/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.36/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.36/0.98      | v2_struct_0(X5)
% 2.36/0.98      | v2_struct_0(X1)
% 2.36/0.98      | v2_struct_0(X4)
% 2.36/0.98      | v2_struct_0(X0)
% 2.36/0.98      | ~ v1_funct_1(X2)
% 2.36/0.98      | ~ l1_pre_topc(X5)
% 2.36/0.98      | ~ l1_pre_topc(X1)
% 2.36/0.98      | ~ v2_pre_topc(X5)
% 2.36/0.98      | ~ v2_pre_topc(X1) ),
% 2.36/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_521,plain,
% 2.36/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 2.36/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.36/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.36/0.98      | ~ v3_pre_topc(X6,X0)
% 2.36/0.98      | ~ m1_pre_topc(X4,X0)
% 2.36/0.98      | ~ m1_pre_topc(X4,X5)
% 2.36/0.98      | ~ m1_pre_topc(X0,X5)
% 2.36/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.36/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.36/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.36/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.36/0.98      | v2_struct_0(X0)
% 2.36/0.98      | v2_struct_0(X1)
% 2.36/0.98      | v2_struct_0(X4)
% 2.36/0.98      | v2_struct_0(X5)
% 2.36/0.98      | ~ v1_funct_1(X2)
% 2.36/0.98      | ~ l1_pre_topc(X1)
% 2.36/0.98      | ~ l1_pre_topc(X5)
% 2.36/0.98      | ~ v2_pre_topc(X1)
% 2.36/0.98      | ~ v2_pre_topc(X5)
% 2.36/0.98      | sK5 != X6
% 2.36/0.98      | sK6 != X3 ),
% 2.36/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_522,plain,
% 2.36/0.98      ( r1_tmap_1(X0,X1,X2,sK6)
% 2.36/0.98      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
% 2.36/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.36/0.98      | ~ v3_pre_topc(sK5,X0)
% 2.36/0.98      | ~ m1_pre_topc(X3,X0)
% 2.36/0.98      | ~ m1_pre_topc(X3,X4)
% 2.36/0.98      | ~ m1_pre_topc(X0,X4)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 2.36/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.36/0.98      | v2_struct_0(X0)
% 2.36/0.98      | v2_struct_0(X1)
% 2.36/0.98      | v2_struct_0(X3)
% 2.36/0.98      | v2_struct_0(X4)
% 2.36/0.98      | ~ v1_funct_1(X2)
% 2.36/0.98      | ~ l1_pre_topc(X1)
% 2.36/0.98      | ~ l1_pre_topc(X4)
% 2.36/0.98      | ~ v2_pre_topc(X1)
% 2.36/0.98      | ~ v2_pre_topc(X4) ),
% 2.36/0.98      inference(unflattening,[status(thm)],[c_521]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_568,plain,
% 2.36/0.98      ( r1_tmap_1(X0,X1,X2,sK6)
% 2.36/0.98      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
% 2.36/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.36/0.98      | ~ v3_pre_topc(sK5,X0)
% 2.36/0.98      | ~ m1_pre_topc(X3,X0)
% 2.36/0.98      | ~ m1_pre_topc(X0,X4)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 2.36/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.36/0.98      | v2_struct_0(X0)
% 2.36/0.98      | v2_struct_0(X1)
% 2.36/0.98      | v2_struct_0(X3)
% 2.36/0.98      | v2_struct_0(X4)
% 2.36/0.98      | ~ v1_funct_1(X2)
% 2.36/0.98      | ~ l1_pre_topc(X1)
% 2.36/0.98      | ~ l1_pre_topc(X4)
% 2.36/0.98      | ~ v2_pre_topc(X1)
% 2.36/0.98      | ~ v2_pre_topc(X4) ),
% 2.36/0.98      inference(forward_subsumption_resolution,
% 2.36/0.98                [status(thm)],
% 2.36/0.98                [c_522,c_10]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_592,plain,
% 2.36/0.98      ( r1_tmap_1(X0,X1,X2,sK6)
% 2.36/0.98      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
% 2.36/0.98      | ~ v3_pre_topc(sK5,X0)
% 2.36/0.98      | ~ m1_pre_topc(X3,X0)
% 2.36/0.98      | ~ m1_pre_topc(X0,X4)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 2.36/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.36/0.98      | v2_struct_0(X0)
% 2.36/0.98      | v2_struct_0(X1)
% 2.36/0.98      | v2_struct_0(X3)
% 2.36/0.98      | v2_struct_0(X4)
% 2.36/0.98      | ~ v1_funct_1(X2)
% 2.36/0.98      | ~ l1_pre_topc(X1)
% 2.36/0.98      | ~ l1_pre_topc(X4)
% 2.36/0.98      | ~ v2_pre_topc(X1)
% 2.36/0.98      | ~ v2_pre_topc(X4)
% 2.36/0.98      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.36/0.98      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.36/0.98      | sK4 != X2 ),
% 2.36/0.98      inference(resolution_lifted,[status(thm)],[c_568,c_24]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_593,plain,
% 2.36/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 2.36/0.98      | r1_tmap_1(X3,X1,sK4,sK6)
% 2.36/0.98      | ~ v3_pre_topc(sK5,X3)
% 2.36/0.98      | ~ m1_pre_topc(X0,X3)
% 2.36/0.98      | ~ m1_pre_topc(X3,X2)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.36/0.98      | v2_struct_0(X3)
% 2.36/0.98      | v2_struct_0(X1)
% 2.36/0.98      | v2_struct_0(X0)
% 2.36/0.98      | v2_struct_0(X2)
% 2.36/0.98      | ~ v1_funct_1(sK4)
% 2.36/0.98      | ~ l1_pre_topc(X1)
% 2.36/0.98      | ~ l1_pre_topc(X2)
% 2.36/0.98      | ~ v2_pre_topc(X1)
% 2.36/0.98      | ~ v2_pre_topc(X2)
% 2.36/0.98      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.36/0.98      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.36/0.98      inference(unflattening,[status(thm)],[c_592]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_597,plain,
% 2.36/0.98      ( v2_struct_0(X2)
% 2.36/0.98      | v2_struct_0(X0)
% 2.36/0.98      | v2_struct_0(X1)
% 2.36/0.98      | v2_struct_0(X3)
% 2.36/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_pre_topc(X3,X2)
% 2.36/0.98      | ~ m1_pre_topc(X0,X3)
% 2.36/0.98      | ~ v3_pre_topc(sK5,X3)
% 2.36/0.98      | r1_tmap_1(X3,X1,sK4,sK6)
% 2.36/0.98      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 2.36/0.98      | ~ l1_pre_topc(X1)
% 2.36/0.98      | ~ l1_pre_topc(X2)
% 2.36/0.98      | ~ v2_pre_topc(X1)
% 2.36/0.98      | ~ v2_pre_topc(X2)
% 2.36/0.98      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.36/0.98      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.36/0.98      inference(global_propositional_subsumption,
% 2.36/0.98                [status(thm)],
% 2.36/0.98                [c_593,c_25]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_598,plain,
% 2.36/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 2.36/0.98      | r1_tmap_1(X3,X1,sK4,sK6)
% 2.36/0.98      | ~ v3_pre_topc(sK5,X3)
% 2.36/0.98      | ~ m1_pre_topc(X3,X2)
% 2.36/0.98      | ~ m1_pre_topc(X0,X3)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.36/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.36/0.98      | v2_struct_0(X0)
% 2.36/0.98      | v2_struct_0(X1)
% 2.36/0.98      | v2_struct_0(X2)
% 2.36/0.98      | v2_struct_0(X3)
% 2.36/0.98      | ~ l1_pre_topc(X1)
% 2.36/0.98      | ~ l1_pre_topc(X2)
% 2.36/0.98      | ~ v2_pre_topc(X1)
% 2.36/0.98      | ~ v2_pre_topc(X2)
% 2.36/0.98      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.36/0.98      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.36/0.98      inference(renaming,[status(thm)],[c_597]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1658,plain,
% 2.36/0.98      ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),sK6)
% 2.36/0.98      | r1_tmap_1(X3_53,X1_53,sK4,sK6)
% 2.36/0.98      | ~ v3_pre_topc(sK5,X3_53)
% 2.36/0.98      | ~ m1_pre_topc(X3_53,X2_53)
% 2.36/0.98      | ~ m1_pre_topc(X0_53,X3_53)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(X0_53))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_53)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X3_53))
% 2.36/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
% 2.36/0.98      | v2_struct_0(X1_53)
% 2.36/0.98      | v2_struct_0(X2_53)
% 2.36/0.98      | v2_struct_0(X3_53)
% 2.36/0.98      | v2_struct_0(X0_53)
% 2.36/0.98      | ~ l1_pre_topc(X1_53)
% 2.36/0.98      | ~ l1_pre_topc(X2_53)
% 2.36/0.98      | ~ v2_pre_topc(X1_53)
% 2.36/0.98      | ~ v2_pre_topc(X2_53)
% 2.36/0.98      | u1_struct_0(X3_53) != u1_struct_0(sK3)
% 2.36/0.98      | u1_struct_0(X1_53) != u1_struct_0(sK0) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_598]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3051,plain,
% 2.36/0.98      ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,sK3,X0_53,sK4),sK6)
% 2.36/0.98      | r1_tmap_1(sK3,X1_53,sK4,sK6)
% 2.36/0.98      | ~ v3_pre_topc(sK5,sK3)
% 2.36/0.98      | ~ m1_pre_topc(X0_53,sK3)
% 2.36/0.98      | ~ m1_pre_topc(sK3,X2_53)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(X0_53))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.36/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
% 2.36/0.98      | v2_struct_0(X1_53)
% 2.36/0.98      | v2_struct_0(X2_53)
% 2.36/0.98      | v2_struct_0(X0_53)
% 2.36/0.98      | v2_struct_0(sK3)
% 2.36/0.98      | ~ l1_pre_topc(X1_53)
% 2.36/0.98      | ~ l1_pre_topc(X2_53)
% 2.36/0.98      | ~ v2_pre_topc(X1_53)
% 2.36/0.98      | ~ v2_pre_topc(X2_53)
% 2.36/0.98      | u1_struct_0(X1_53) != u1_struct_0(sK0)
% 2.36/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1658]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_4441,plain,
% 2.36/0.98      ( r1_tmap_1(sK3,X0_53,sK4,sK6)
% 2.36/0.98      | ~ r1_tmap_1(sK2,X0_53,k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4),sK6)
% 2.36/0.98      | ~ v3_pre_topc(sK5,sK3)
% 2.36/0.98      | ~ m1_pre_topc(sK3,X1_53)
% 2.36/0.98      | ~ m1_pre_topc(sK2,sK3)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 2.36/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 2.36/0.98      | v2_struct_0(X1_53)
% 2.36/0.98      | v2_struct_0(X0_53)
% 2.36/0.98      | v2_struct_0(sK3)
% 2.36/0.98      | v2_struct_0(sK2)
% 2.36/0.98      | ~ l1_pre_topc(X1_53)
% 2.36/0.98      | ~ l1_pre_topc(X0_53)
% 2.36/0.98      | ~ v2_pre_topc(X1_53)
% 2.36/0.98      | ~ v2_pre_topc(X0_53)
% 2.36/0.98      | u1_struct_0(X0_53) != u1_struct_0(sK0)
% 2.36/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_3051]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_4742,plain,
% 2.36/0.98      ( r1_tmap_1(sK3,X0_53,sK4,sK6)
% 2.36/0.98      | ~ r1_tmap_1(sK2,X0_53,k3_tmap_1(sK1,X0_53,sK3,sK2,sK4),sK6)
% 2.36/0.98      | ~ v3_pre_topc(sK5,sK3)
% 2.36/0.98      | ~ m1_pre_topc(sK3,sK1)
% 2.36/0.98      | ~ m1_pre_topc(sK2,sK3)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 2.36/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 2.36/0.98      | v2_struct_0(X0_53)
% 2.36/0.98      | v2_struct_0(sK3)
% 2.36/0.98      | v2_struct_0(sK1)
% 2.36/0.98      | v2_struct_0(sK2)
% 2.36/0.98      | ~ l1_pre_topc(X0_53)
% 2.36/0.98      | ~ l1_pre_topc(sK1)
% 2.36/0.98      | ~ v2_pre_topc(X0_53)
% 2.36/0.98      | ~ v2_pre_topc(sK1)
% 2.36/0.98      | u1_struct_0(X0_53) != u1_struct_0(sK0)
% 2.36/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_4441]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_4744,plain,
% 2.36/0.98      ( r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.36/0.98      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 2.36/0.98      | ~ v3_pre_topc(sK5,sK3)
% 2.36/0.98      | ~ m1_pre_topc(sK3,sK1)
% 2.36/0.98      | ~ m1_pre_topc(sK2,sK3)
% 2.36/0.98      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.36/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 2.36/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
% 2.36/0.98      | v2_struct_0(sK3)
% 2.36/0.98      | v2_struct_0(sK1)
% 2.36/0.98      | v2_struct_0(sK0)
% 2.36/0.98      | v2_struct_0(sK2)
% 2.36/0.98      | ~ l1_pre_topc(sK1)
% 2.36/0.98      | ~ l1_pre_topc(sK0)
% 2.36/0.98      | ~ v2_pre_topc(sK1)
% 2.36/0.98      | ~ v2_pre_topc(sK0)
% 2.36/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.36/0.98      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_4742]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1700,plain,
% 2.36/0.98      ( ~ r1_tmap_1(X0_53,X1_53,X0_54,X1_54)
% 2.36/0.98      | r1_tmap_1(X0_53,X1_53,X2_54,X3_54)
% 2.36/0.98      | X2_54 != X0_54
% 2.36/0.98      | X3_54 != X1_54 ),
% 2.36/0.98      theory(equality) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3722,plain,
% 2.36/0.98      ( r1_tmap_1(sK2,X0_53,X0_54,X1_54)
% 2.36/0.98      | ~ r1_tmap_1(sK2,X0_53,k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4),sK6)
% 2.36/0.98      | X0_54 != k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4)
% 2.36/0.98      | X1_54 != sK6 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1700]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3895,plain,
% 2.36/0.98      ( r1_tmap_1(sK2,X0_53,X0_54,sK7)
% 2.36/0.98      | ~ r1_tmap_1(sK2,X0_53,k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4),sK6)
% 2.36/0.98      | X0_54 != k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4)
% 2.36/0.98      | sK7 != sK6 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_3722]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_4523,plain,
% 2.36/0.98      ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X0_54),sK7)
% 2.36/0.98      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 2.36/0.98      | k3_tmap_1(sK1,sK0,sK3,sK2,X0_54) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 2.36/0.98      | sK7 != sK6 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_3895]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_4525,plain,
% 2.36/0.98      ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 2.36/0.98      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 2.36/0.98      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 2.36/0.98      | sK7 != sK6 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_4523]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3824,plain,
% 2.36/0.98      ( r1_tmap_1(sK3,sK0,X0_54,X1_54)
% 2.36/0.98      | ~ r1_tmap_1(sK3,sK0,X2_54,sK7)
% 2.36/0.98      | X0_54 != X2_54
% 2.36/0.98      | X1_54 != sK7 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1700]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_4479,plain,
% 2.36/0.98      ( r1_tmap_1(sK3,sK0,X0_54,sK6)
% 2.36/0.98      | ~ r1_tmap_1(sK3,sK0,X1_54,sK7)
% 2.36/0.98      | X0_54 != X1_54
% 2.36/0.98      | sK6 != sK7 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_3824]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_4481,plain,
% 2.36/0.98      ( r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.36/0.98      | ~ r1_tmap_1(sK3,sK0,sK4,sK7)
% 2.36/0.98      | sK6 != sK7
% 2.36/0.98      | sK4 != sK4 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_4479]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1689,plain,( X0_55 = X0_55 ),theory(equality) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3813,plain,
% 2.36/0.98      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1689]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3338,plain,
% 2.36/0.98      ( r1_tmap_1(sK3,sK0,X0_54,X1_54)
% 2.36/0.98      | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.36/0.98      | X1_54 != sK6
% 2.36/0.98      | X0_54 != sK4 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1700]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3798,plain,
% 2.36/0.98      ( r1_tmap_1(sK3,sK0,X0_54,sK7)
% 2.36/0.98      | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.36/0.98      | X0_54 != sK4
% 2.36/0.98      | sK7 != sK6 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_3338]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3800,plain,
% 2.36/0.98      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.36/0.98      | r1_tmap_1(sK3,sK0,sK4,sK7)
% 2.36/0.98      | sK7 != sK6
% 2.36/0.98      | sK4 != sK4 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_3798]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1690,plain,
% 2.36/0.98      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 2.36/0.98      theory(equality) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2994,plain,
% 2.36/0.98      ( X0_54 != X1_54 | X0_54 = sK6 | sK6 != X1_54 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1690]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3213,plain,
% 2.36/0.98      ( X0_54 = sK6 | X0_54 != sK7 | sK6 != sK7 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_2994]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3302,plain,
% 2.36/0.98      ( sK6 != sK7 | sK7 = sK6 | sK7 != sK7 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_3213]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3,plain,
% 2.36/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.36/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1683,plain,
% 2.36/0.98      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.36/0.98      | ~ l1_pre_topc(X1_53)
% 2.36/0.98      | l1_pre_topc(X0_53) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3046,plain,
% 2.36/0.98      ( ~ m1_pre_topc(sK3,X0_53)
% 2.36/0.98      | ~ l1_pre_topc(X0_53)
% 2.36/0.98      | l1_pre_topc(sK3) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1683]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3256,plain,
% 2.36/0.98      ( ~ m1_pre_topc(sK3,sK1) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK1) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_3046]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_4,plain,
% 2.36/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.36/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.36/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/0.98      | ~ l1_pre_topc(X1) ),
% 2.36/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1682,plain,
% 2.36/0.98      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.36/0.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.36/0.98      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X1_53)))
% 2.36/0.98      | ~ l1_pre_topc(X1_53) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2936,plain,
% 2.36/0.98      ( ~ m1_pre_topc(sK2,X0_53)
% 2.36/0.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.36/0.98      | ~ l1_pre_topc(X0_53) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1682]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3162,plain,
% 2.36/0.98      ( ~ m1_pre_topc(sK2,sK3)
% 2.36/0.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.36/0.98      | ~ l1_pre_topc(sK3) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_2936]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1688,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3102,plain,
% 2.36/0.98      ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1688]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2919,plain,
% 2.36/0.98      ( r1_tmap_1(sK2,sK0,X0_54,X1_54)
% 2.36/0.98      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 2.36/0.98      | X0_54 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 2.36/0.98      | X1_54 != sK7 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1700]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3020,plain,
% 2.36/0.98      ( r1_tmap_1(sK2,sK0,X0_54,sK6)
% 2.36/0.98      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 2.36/0.98      | X0_54 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 2.36/0.98      | sK6 != sK7 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_2919]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3101,plain,
% 2.36/0.98      ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 2.36/0.98      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 2.36/0.98      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 2.36/0.98      | sK6 != sK7 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_3020]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3096,plain,
% 2.36/0.98      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1689]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1693,plain,
% 2.36/0.98      ( ~ m1_subset_1(X0_54,X0_55)
% 2.36/0.98      | m1_subset_1(X1_54,X1_55)
% 2.36/0.98      | X1_55 != X0_55
% 2.36/0.98      | X1_54 != X0_54 ),
% 2.36/0.98      theory(equality) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2885,plain,
% 2.36/0.98      ( m1_subset_1(X0_54,X0_55)
% 2.36/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK2))
% 2.36/0.98      | X0_55 != u1_struct_0(sK2)
% 2.36/0.98      | X0_54 != sK7 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1693]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2975,plain,
% 2.36/0.98      ( m1_subset_1(sK6,X0_55)
% 2.36/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK2))
% 2.36/0.98      | X0_55 != u1_struct_0(sK2)
% 2.36/0.98      | sK6 != sK7 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_2885]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_3095,plain,
% 2.36/0.98      ( m1_subset_1(sK6,u1_struct_0(sK2))
% 2.36/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK2))
% 2.36/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.36/0.98      | sK6 != sK7 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_2975]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2981,plain,
% 2.36/0.98      ( sK7 = sK7 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1688]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_5,plain,
% 2.36/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.36/0.98      | v3_pre_topc(X0,X2)
% 2.36/0.98      | ~ m1_pre_topc(X2,X1)
% 2.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/0.98      | ~ l1_pre_topc(X1) ),
% 2.36/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1681,plain,
% 2.36/0.98      ( ~ v3_pre_topc(X0_54,X0_53)
% 2.36/0.98      | v3_pre_topc(X0_54,X1_53)
% 2.36/0.98      | ~ m1_pre_topc(X1_53,X0_53)
% 2.36/0.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X1_53)))
% 2.36/0.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.36/0.98      | ~ l1_pre_topc(X0_53) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2914,plain,
% 2.36/0.98      ( v3_pre_topc(sK5,X0_53)
% 2.36/0.98      | ~ v3_pre_topc(sK5,sK1)
% 2.36/0.98      | ~ m1_pre_topc(X0_53,sK1)
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.36/0.98      | ~ l1_pre_topc(sK1) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1681]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2965,plain,
% 2.36/0.98      ( v3_pre_topc(sK5,sK3)
% 2.36/0.98      | ~ v3_pre_topc(sK5,sK1)
% 2.36/0.98      | ~ m1_pre_topc(sK3,sK1)
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.36/0.98      | ~ l1_pre_topc(sK1) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_2914]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2850,plain,
% 2.36/0.98      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1689]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_14,negated_conjecture,
% 2.36/0.98      ( r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.36/0.98      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 2.36/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1677,negated_conjecture,
% 2.36/0.98      ( r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.36/0.98      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2477,plain,
% 2.36/0.98      ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 2.36/0.98      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
% 2.36/0.98      inference(predicate_to_equality,[status(thm)],[c_1677]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_15,negated_conjecture,
% 2.36/0.98      ( sK6 = sK7 ),
% 2.36/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1676,negated_conjecture,
% 2.36/0.98      ( sK6 = sK7 ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2555,plain,
% 2.36/0.98      ( r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
% 2.36/0.98      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
% 2.36/0.98      inference(light_normalisation,[status(thm)],[c_2477,c_1676]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2789,plain,
% 2.36/0.98      ( r1_tmap_1(sK3,sK0,sK4,sK7)
% 2.36/0.98      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 2.36/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2555]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_13,negated_conjecture,
% 2.36/0.98      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.36/0.98      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 2.36/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1678,negated_conjecture,
% 2.36/0.98      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.36/0.98      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 2.36/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2476,plain,
% 2.36/0.98      ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
% 2.36/0.98      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
% 2.36/0.98      inference(predicate_to_equality,[status(thm)],[c_1678]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2560,plain,
% 2.36/0.98      ( r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
% 2.36/0.98      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
% 2.36/0.98      inference(light_normalisation,[status(thm)],[c_2476,c_1676]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_2786,plain,
% 2.36/0.98      ( ~ r1_tmap_1(sK3,sK0,sK4,sK7)
% 2.36/0.98      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 2.36/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2560]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_1711,plain,
% 2.36/0.98      ( sK4 = sK4 ),
% 2.36/0.98      inference(instantiation,[status(thm)],[c_1688]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_0,plain,
% 2.36/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.36/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_234,plain,
% 2.36/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.36/0.98      inference(prop_impl,[status(thm)],[c_0]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_16,negated_conjecture,
% 2.36/0.98      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 2.36/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_892,plain,
% 2.36/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.36/0.98      | u1_struct_0(sK2) != X1
% 2.36/0.98      | sK5 != X0 ),
% 2.36/0.98      inference(resolution_lifted,[status(thm)],[c_234,c_16]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_893,plain,
% 2.36/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.36/0.98      inference(unflattening,[status(thm)],[c_892]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_18,negated_conjecture,
% 2.36/0.98      ( v3_pre_topc(sK5,sK1) ),
% 2.36/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_19,negated_conjecture,
% 2.36/0.98      ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
% 2.36/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_20,negated_conjecture,
% 2.36/0.98      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.36/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_21,negated_conjecture,
% 2.36/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.36/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_22,negated_conjecture,
% 2.36/0.98      ( m1_pre_topc(sK2,sK3) ),
% 2.36/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_23,negated_conjecture,
% 2.36/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
% 2.36/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_26,negated_conjecture,
% 2.36/0.98      ( m1_pre_topc(sK3,sK1) ),
% 2.36/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_27,negated_conjecture,
% 2.36/0.98      ( ~ v2_struct_0(sK3) ),
% 2.36/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_29,negated_conjecture,
% 2.36/0.98      ( ~ v2_struct_0(sK2) ),
% 2.36/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_30,negated_conjecture,
% 2.36/0.98      ( l1_pre_topc(sK1) ),
% 2.36/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_31,negated_conjecture,
% 2.36/0.98      ( v2_pre_topc(sK1) ),
% 2.36/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_32,negated_conjecture,
% 2.36/0.98      ( ~ v2_struct_0(sK1) ),
% 2.36/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_33,negated_conjecture,
% 2.36/0.98      ( l1_pre_topc(sK0) ),
% 2.36/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_34,negated_conjecture,
% 2.36/0.98      ( v2_pre_topc(sK0) ),
% 2.36/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(c_35,negated_conjecture,
% 2.36/0.98      ( ~ v2_struct_0(sK0) ),
% 2.36/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.36/0.98  
% 2.36/0.98  cnf(contradiction,plain,
% 2.36/0.98      ( $false ),
% 2.36/0.98      inference(minisat,
% 2.36/0.98                [status(thm)],
% 2.36/0.98                [c_4909,c_4744,c_4525,c_4481,c_3813,c_3800,c_3302,c_3256,
% 2.36/0.98                 c_3162,c_3102,c_3101,c_3096,c_3095,c_2981,c_2965,c_2850,
% 2.36/0.98                 c_2789,c_2786,c_1676,c_1711,c_893,c_16,c_18,c_19,c_20,
% 2.36/0.98                 c_21,c_22,c_23,c_26,c_27,c_29,c_30,c_31,c_32,c_33,c_34,
% 2.36/0.98                 c_35]) ).
% 2.36/0.98  
% 2.36/0.98  
% 2.36/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.36/0.98  
% 2.36/0.98  ------                               Statistics
% 2.36/0.98  
% 2.36/0.98  ------ General
% 2.36/0.98  
% 2.36/0.98  abstr_ref_over_cycles:                  0
% 2.36/0.98  abstr_ref_under_cycles:                 0
% 2.36/0.98  gc_basic_clause_elim:                   0
% 2.36/0.98  forced_gc_time:                         0
% 2.36/0.98  parsing_time:                           0.013
% 2.36/0.98  unif_index_cands_time:                  0.
% 2.36/0.98  unif_index_add_time:                    0.
% 2.36/0.98  orderings_time:                         0.
% 2.36/0.98  out_proof_time:                         0.014
% 2.36/0.98  total_time:                             0.182
% 2.36/0.98  num_of_symbols:                         59
% 2.36/0.98  num_of_terms:                           2849
% 2.36/0.98  
% 2.36/0.98  ------ Preprocessing
% 2.36/0.98  
% 2.36/0.98  num_of_splits:                          0
% 2.36/0.98  num_of_split_atoms:                     0
% 2.36/0.98  num_of_reused_defs:                     0
% 2.36/0.98  num_eq_ax_congr_red:                    24
% 2.36/0.98  num_of_sem_filtered_clauses:            1
% 2.36/0.98  num_of_subtypes:                        3
% 2.36/0.98  monotx_restored_types:                  0
% 2.36/0.98  sat_num_of_epr_types:                   0
% 2.36/0.98  sat_num_of_non_cyclic_types:            0
% 2.36/0.98  sat_guarded_non_collapsed_types:        0
% 2.36/0.98  num_pure_diseq_elim:                    0
% 2.36/0.98  simp_replaced_by:                       0
% 2.36/0.98  res_preprocessed:                       162
% 2.36/0.98  prep_upred:                             0
% 2.36/0.98  prep_unflattend:                        21
% 2.36/0.98  smt_new_axioms:                         0
% 2.36/0.98  pred_elim_cands:                        8
% 2.36/0.98  pred_elim:                              3
% 2.36/0.98  pred_elim_cl:                           3
% 2.36/0.98  pred_elim_cycles:                       5
% 2.36/0.98  merged_defs:                            16
% 2.36/0.98  merged_defs_ncl:                        0
% 2.36/0.98  bin_hyper_res:                          16
% 2.36/0.98  prep_cycles:                            4
% 2.36/0.98  pred_elim_time:                         0.035
% 2.36/0.98  splitting_time:                         0.
% 2.36/0.98  sem_filter_time:                        0.
% 2.36/0.98  monotx_time:                            0.
% 2.36/0.98  subtype_inf_time:                       0.
% 2.36/0.98  
% 2.36/0.98  ------ Problem properties
% 2.36/0.98  
% 2.36/0.98  clauses:                                33
% 2.36/0.98  conjectures:                            20
% 2.36/0.98  epr:                                    17
% 2.36/0.98  horn:                                   27
% 2.36/0.98  ground:                                 20
% 2.36/0.98  unary:                                  18
% 2.36/0.98  binary:                                 5
% 2.36/0.98  lits:                                   128
% 2.36/0.98  lits_eq:                                13
% 2.36/0.98  fd_pure:                                0
% 2.36/0.98  fd_pseudo:                              0
% 2.36/0.98  fd_cond:                                0
% 2.36/0.98  fd_pseudo_cond:                         0
% 2.36/0.98  ac_symbols:                             0
% 2.36/0.98  
% 2.36/0.98  ------ Propositional Solver
% 2.36/0.98  
% 2.36/0.98  prop_solver_calls:                      28
% 2.36/0.98  prop_fast_solver_calls:                 1878
% 2.36/0.98  smt_solver_calls:                       0
% 2.36/0.98  smt_fast_solver_calls:                  0
% 2.36/0.98  prop_num_of_clauses:                    1075
% 2.36/0.98  prop_preprocess_simplified:             4507
% 2.36/0.98  prop_fo_subsumed:                       40
% 2.36/0.98  prop_solver_time:                       0.
% 2.36/0.98  smt_solver_time:                        0.
% 2.36/0.98  smt_fast_solver_time:                   0.
% 2.36/0.98  prop_fast_solver_time:                  0.
% 2.36/0.98  prop_unsat_core_time:                   0.
% 2.36/0.98  
% 2.36/0.98  ------ QBF
% 2.36/0.98  
% 2.36/0.98  qbf_q_res:                              0
% 2.36/0.98  qbf_num_tautologies:                    0
% 2.36/0.98  qbf_prep_cycles:                        0
% 2.36/0.98  
% 2.36/0.98  ------ BMC1
% 2.36/0.98  
% 2.36/0.98  bmc1_current_bound:                     -1
% 2.36/0.98  bmc1_last_solved_bound:                 -1
% 2.36/0.98  bmc1_unsat_core_size:                   -1
% 2.36/0.98  bmc1_unsat_core_parents_size:           -1
% 2.36/0.98  bmc1_merge_next_fun:                    0
% 2.36/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.36/0.98  
% 2.36/0.98  ------ Instantiation
% 2.36/0.98  
% 2.36/0.98  inst_num_of_clauses:                    306
% 2.36/0.98  inst_num_in_passive:                    32
% 2.36/0.98  inst_num_in_active:                     252
% 2.36/0.98  inst_num_in_unprocessed:                21
% 2.36/0.98  inst_num_of_loops:                      293
% 2.36/0.98  inst_num_of_learning_restarts:          0
% 2.36/0.98  inst_num_moves_active_passive:          34
% 2.36/0.98  inst_lit_activity:                      0
% 2.36/0.98  inst_lit_activity_moves:                0
% 2.36/0.98  inst_num_tautologies:                   0
% 2.36/0.98  inst_num_prop_implied:                  0
% 2.36/0.98  inst_num_existing_simplified:           0
% 2.36/0.98  inst_num_eq_res_simplified:             0
% 2.36/0.98  inst_num_child_elim:                    0
% 2.36/0.98  inst_num_of_dismatching_blockings:      20
% 2.36/0.98  inst_num_of_non_proper_insts:           353
% 2.36/0.98  inst_num_of_duplicates:                 0
% 2.36/0.98  inst_inst_num_from_inst_to_res:         0
% 2.36/0.98  inst_dismatching_checking_time:         0.
% 2.36/0.98  
% 2.36/0.98  ------ Resolution
% 2.36/0.98  
% 2.36/0.98  res_num_of_clauses:                     0
% 2.36/0.98  res_num_in_passive:                     0
% 2.36/0.98  res_num_in_active:                      0
% 2.36/0.98  res_num_of_loops:                       166
% 2.36/0.98  res_forward_subset_subsumed:            87
% 2.36/0.98  res_backward_subset_subsumed:           0
% 2.36/0.98  res_forward_subsumed:                   0
% 2.36/0.98  res_backward_subsumed:                  0
% 2.36/0.98  res_forward_subsumption_resolution:     2
% 2.36/0.98  res_backward_subsumption_resolution:    0
% 2.36/0.98  res_clause_to_clause_subsumption:       450
% 2.36/0.98  res_orphan_elimination:                 0
% 2.36/0.98  res_tautology_del:                      123
% 2.36/0.98  res_num_eq_res_simplified:              0
% 2.36/0.98  res_num_sel_changes:                    0
% 2.36/0.98  res_moves_from_active_to_pass:          0
% 2.36/0.98  
% 2.36/0.98  ------ Superposition
% 2.36/0.98  
% 2.36/0.98  sup_time_total:                         0.
% 2.36/0.98  sup_time_generating:                    0.
% 2.36/0.98  sup_time_sim_full:                      0.
% 2.36/0.98  sup_time_sim_immed:                     0.
% 2.36/0.98  
% 2.36/0.98  sup_num_of_clauses:                     71
% 2.36/0.98  sup_num_in_active:                      58
% 2.36/0.98  sup_num_in_passive:                     13
% 2.36/0.98  sup_num_of_loops:                       58
% 2.36/0.98  sup_fw_superposition:                   40
% 2.36/0.98  sup_bw_superposition:                   14
% 2.36/0.98  sup_immediate_simplified:               11
% 2.36/0.98  sup_given_eliminated:                   0
% 2.36/0.98  comparisons_done:                       0
% 2.36/0.98  comparisons_avoided:                    0
% 2.36/0.98  
% 2.36/0.98  ------ Simplifications
% 2.36/0.98  
% 2.36/0.98  
% 2.36/0.98  sim_fw_subset_subsumed:                 11
% 2.36/0.98  sim_bw_subset_subsumed:                 0
% 2.36/0.98  sim_fw_subsumed:                        0
% 2.36/0.98  sim_bw_subsumed:                        0
% 2.36/0.98  sim_fw_subsumption_res:                 2
% 2.36/0.98  sim_bw_subsumption_res:                 0
% 2.36/0.98  sim_tautology_del:                      5
% 2.36/0.98  sim_eq_tautology_del:                   0
% 2.36/0.98  sim_eq_res_simp:                        0
% 2.36/0.98  sim_fw_demodulated:                     0
% 2.36/0.98  sim_bw_demodulated:                     0
% 2.36/0.98  sim_light_normalised:                   5
% 2.36/0.98  sim_joinable_taut:                      0
% 2.36/0.98  sim_joinable_simp:                      0
% 2.36/0.98  sim_ac_normalised:                      0
% 2.36/0.98  sim_smt_subsumption:                    0
% 2.36/0.98  
%------------------------------------------------------------------------------
