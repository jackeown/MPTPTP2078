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
% DateTime   : Thu Dec  3 12:23:13 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 693 expanded)
%              Number of clauses        :  123 ( 144 expanded)
%              Number of leaves         :   25 ( 303 expanded)
%              Depth                    :   22
%              Number of atoms          : 1732 (14506 expanded)
%              Number of equality atoms :  210 ( 914 expanded)
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
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
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
    inference(equality_resolution,[],[f59])).

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

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
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
    inference(equality_resolution,[],[f56])).

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

fof(f22,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(cnf_transformation,[],[f23])).

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

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f20,plain,(
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
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f80,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f82,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,(
    v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
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

cnf(c_1773,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,X0_54,X1_54)
    | r1_tmap_1(X0_53,X1_53,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_3345,plain,
    ( r1_tmap_1(sK2,sK0,X0_54,X1_54)
    | ~ r1_tmap_1(sK2,sK0,X2_54,sK6)
    | X0_54 != X2_54
    | X1_54 != sK6 ),
    inference(instantiation,[status(thm)],[c_1773])).

cnf(c_3722,plain,
    ( ~ r1_tmap_1(sK2,sK0,X0_54,sK6)
    | r1_tmap_1(sK2,sK0,X1_54,sK7)
    | X1_54 != X0_54
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_3345])).

cnf(c_4576,plain,
    ( r1_tmap_1(sK2,sK0,X0_54,sK7)
    | ~ r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK6)
    | X0_54 != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_3722])).

cnf(c_5062,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK6)
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_4576])).

cnf(c_3719,plain,
    ( ~ r1_tmap_1(sK2,sK0,X0_54,sK6)
    | r1_tmap_1(sK2,sK0,X1_54,sK6)
    | X1_54 != X0_54
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_3345])).

cnf(c_4193,plain,
    ( r1_tmap_1(sK2,sK0,X0_54,sK6)
    | ~ r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | X0_54 != k2_tmap_1(sK3,sK0,sK4,sK2)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_3719])).

cnf(c_5029,plain,
    ( r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK6)
    | ~ r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) != k2_tmap_1(sK3,sK0,sK4,sK2)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4193])).

cnf(c_1763,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_3807,plain,
    ( X0_54 != X1_54
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != X1_54
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = X0_54 ),
    inference(instantiation,[status(thm)],[c_1763])).

cnf(c_4124,plain,
    ( X0_54 != k3_tmap_1(sK1,sK0,sK3,sK2,X1_54)
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = X0_54
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,X1_54) ),
    inference(instantiation,[status(thm)],[c_3807])).

cnf(c_4527,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_4124])).

cnf(c_11,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r2_hidden(X3,X6)
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
    inference(cnf_transformation,[],[f78])).

cnf(c_533,plain,
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

cnf(c_534,plain,
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
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_453,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | sK5 != X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_17])).

cnf(c_454,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | m1_subset_1(sK6,X0) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_559,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_534,c_454])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_580,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X0,X4)
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
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
    inference(forward_subsumption_resolution,[status(thm)],[c_559,c_10])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_606,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X0,X4)
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
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
    inference(resolution_lifted,[status(thm)],[c_580,c_24])).

cnf(c_607,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | r1_tmap_1(X3,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
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
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_611,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
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
    inference(global_propositional_subsumption,[status(thm)],[c_607,c_25])).

cnf(c_612,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | r1_tmap_1(X3,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
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
    inference(renaming,[status(thm)],[c_611])).

cnf(c_1731,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),sK6)
    | r1_tmap_1(X3_53,X1_53,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3_53)
    | ~ m1_pre_topc(X3_53,X2_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ r1_tarski(sK5,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_53)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
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
    inference(subtyping,[status(esa)],[c_612])).

cnf(c_3670,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,sK3,X0_53,sK4),sK6)
    | r1_tmap_1(sK3,X1_53,sK4,sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(X0_53,sK3)
    | ~ m1_pre_topc(sK3,X2_53)
    | ~ r1_tarski(sK5,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
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
    inference(instantiation,[status(thm)],[c_1731])).

cnf(c_3899,plain,
    ( r1_tmap_1(sK3,X0_53,sK4,sK6)
    | ~ r1_tmap_1(sK2,X0_53,k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4),sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK3,X1_53)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
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
    inference(instantiation,[status(thm)],[c_3670])).

cnf(c_4204,plain,
    ( r1_tmap_1(sK3,X0_53,sK4,sK6)
    | ~ r1_tmap_1(sK2,X0_53,k3_tmap_1(sK1,X0_53,sK3,sK2,sK4),sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
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
    inference(instantiation,[status(thm)],[c_3899])).

cnf(c_4206,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
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
    inference(instantiation,[status(thm)],[c_4204])).

cnf(c_3021,plain,
    ( r1_tmap_1(sK2,sK0,X0_54,X1_54)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | X0_54 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | X1_54 != sK7 ),
    inference(instantiation,[status(thm)],[c_1773])).

cnf(c_3197,plain,
    ( r1_tmap_1(sK2,sK0,X0_54,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | X0_54 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_3021])).

cnf(c_3975,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_3197])).

cnf(c_9,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_744,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_745,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
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
    inference(unflattening,[status(thm)],[c_744])).

cnf(c_749,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_745,c_25])).

cnf(c_750,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_749])).

cnf(c_1729,plain,
    ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,sK4,X0_53),X0_54)
    | ~ r1_tmap_1(X2_53,X1_53,sK4,X0_54)
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(X2_53))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X2_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_750])).

cnf(c_3213,plain,
    ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK3,X1_53,sK4,X0_53),X0_54)
    | ~ r1_tmap_1(sK3,X1_53,sK4,X0_54)
    | ~ m1_pre_topc(X0_53,sK3)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1729])).

cnf(c_3736,plain,
    ( ~ r1_tmap_1(sK3,X0_53,sK4,X0_54)
    | r1_tmap_1(sK2,X0_53,k2_tmap_1(sK3,X0_53,sK4,sK2),X0_54)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3213])).

cnf(c_3888,plain,
    ( ~ r1_tmap_1(sK3,X0_53,sK4,sK6)
    | r1_tmap_1(sK2,X0_53,k2_tmap_1(sK3,X0_53,sK4,sK2),sK6)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3736])).

cnf(c_3890,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3888])).

cnf(c_1762,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_3828,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1762])).

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

cnf(c_849,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
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

cnf(c_850,plain,
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
    inference(unflattening,[status(thm)],[c_849])).

cnf(c_854,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_850,c_25])).

cnf(c_855,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_854])).

cnf(c_1727,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X2_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X1_53) != u1_struct_0(sK3)
    | u1_struct_0(X2_53) != u1_struct_0(sK0)
    | k2_partfun1(u1_struct_0(X1_53),u1_struct_0(X2_53),sK4,u1_struct_0(X0_53)) = k2_tmap_1(X1_53,X2_53,sK4,X0_53) ),
    inference(subtyping,[status(esa)],[c_855])).

cnf(c_2923,plain,
    ( ~ m1_pre_topc(X0_53,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1_53),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK3,X1_53,sK4,X0_53) ),
    inference(instantiation,[status(thm)],[c_1727])).

cnf(c_3731,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0_53),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,X0_53,sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_2923])).

cnf(c_3733,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK0,sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_3731])).

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

cnf(c_801,plain,
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

cnf(c_802,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK4,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_801])).

cnf(c_806,plain,
    ( v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK4,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_802,c_25,c_10])).

cnf(c_807,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK4,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_806])).

cnf(c_1728,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_pre_topc(X2_53,X0_53)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X3_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X3_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X3_53)
    | u1_struct_0(X0_53) != u1_struct_0(sK3)
    | u1_struct_0(X3_53) != u1_struct_0(sK0)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X3_53),sK4,u1_struct_0(X2_53)) = k3_tmap_1(X1_53,X3_53,X0_53,X2_53,sK4) ),
    inference(subtyping,[status(esa)],[c_807])).

cnf(c_3208,plain,
    ( ~ m1_pre_topc(X0_53,sK3)
    | ~ m1_pre_topc(sK3,X1_53)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2_53))))
    | v2_struct_0(X2_53)
    | v2_struct_0(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | u1_struct_0(X2_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X2_53),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,X2_53,sK3,X0_53,sK4) ),
    inference(instantiation,[status(thm)],[c_1728])).

cnf(c_3445,plain,
    ( ~ m1_pre_topc(sK3,X0_53)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X0_53)
    | u1_struct_0(X1_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1_53),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0_53,X1_53,sK3,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_3208])).

cnf(c_3652,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_53) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0_53),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK1,X0_53,sK3,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_3445])).

cnf(c_3654,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_3652])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1742,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_2559,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1742])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1757,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v2_pre_topc(X1_53)
    | v2_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2545,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1757])).

cnf(c_3521,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2559,c_2545])).

cnf(c_3542,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3521])).

cnf(c_1772,plain,
    ( X0_54 != X1_54
    | k3_tmap_1(X0_53,X1_53,X2_53,X3_53,X0_54) = k3_tmap_1(X0_53,X1_53,X2_53,X3_53,X1_54) ),
    theory(equality)).

cnf(c_3427,plain,
    ( X0_54 != sK4
    | k3_tmap_1(sK1,sK0,sK3,sK2,X0_54) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1772])).

cnf(c_3430,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3427])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1756,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3247,plain,
    ( ~ m1_pre_topc(sK3,X0_53)
    | ~ l1_pre_topc(X0_53)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1756])).

cnf(c_3375,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3247])).

cnf(c_3144,plain,
    ( X0_54 != X1_54
    | X0_54 = sK6
    | sK6 != X1_54 ),
    inference(instantiation,[status(thm)],[c_1763])).

cnf(c_3320,plain,
    ( X0_54 = sK6
    | X0_54 != sK7
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_3144])).

cnf(c_3354,plain,
    ( sK6 != sK7
    | sK7 = sK6
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3320])).

cnf(c_1761,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_3139,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1761])).

cnf(c_3127,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1761])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1755,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X1_53)))
    | ~ l1_pre_topc(X1_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2957,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1755])).

cnf(c_3115,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2957])).

cnf(c_6,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1754,plain,
    ( ~ v3_pre_topc(X0_54,X0_53)
    | v3_pre_topc(X0_54,X1_53)
    | ~ m1_pre_topc(X1_53,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X1_53)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3016,plain,
    ( v3_pre_topc(sK5,X0_53)
    | ~ v3_pre_topc(sK5,sK1)
    | ~ m1_pre_topc(X0_53,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1754])).

cnf(c_3114,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ v3_pre_topc(sK5,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3016])).

cnf(c_1732,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0_55))
    | m1_subset_1(sK6,X0_55) ),
    inference(subtyping,[status(esa)],[c_454])).

cnf(c_3048,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1732])).

cnf(c_2922,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_15,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1750,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1784,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1761])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_233,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_900,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | u1_struct_0(sK2) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_233,c_16])).

cnf(c_901,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_900])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_14,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_18,negated_conjecture,
    ( v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5062,c_5029,c_4527,c_4206,c_3975,c_3890,c_3828,c_3733,c_3654,c_3542,c_3430,c_3375,c_3354,c_3139,c_3127,c_3115,c_3114,c_3048,c_2922,c_1750,c_1784,c_901,c_13,c_14,c_16,c_18,c_20,c_21,c_22,c_23,c_26,c_27,c_29,c_30,c_31,c_32,c_33,c_34,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:51:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.22/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.02  
% 2.22/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.22/1.02  
% 2.22/1.02  ------  iProver source info
% 2.22/1.02  
% 2.22/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.22/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.22/1.02  git: non_committed_changes: false
% 2.22/1.02  git: last_make_outside_of_git: false
% 2.22/1.02  
% 2.22/1.02  ------ 
% 2.22/1.02  
% 2.22/1.02  ------ Input Options
% 2.22/1.02  
% 2.22/1.02  --out_options                           all
% 2.22/1.02  --tptp_safe_out                         true
% 2.22/1.02  --problem_path                          ""
% 2.22/1.02  --include_path                          ""
% 2.22/1.02  --clausifier                            res/vclausify_rel
% 2.22/1.02  --clausifier_options                    --mode clausify
% 2.22/1.02  --stdin                                 false
% 2.22/1.02  --stats_out                             all
% 2.22/1.02  
% 2.22/1.02  ------ General Options
% 2.22/1.02  
% 2.22/1.02  --fof                                   false
% 2.22/1.02  --time_out_real                         305.
% 2.22/1.02  --time_out_virtual                      -1.
% 2.22/1.02  --symbol_type_check                     false
% 2.22/1.02  --clausify_out                          false
% 2.22/1.02  --sig_cnt_out                           false
% 2.22/1.02  --trig_cnt_out                          false
% 2.22/1.02  --trig_cnt_out_tolerance                1.
% 2.22/1.02  --trig_cnt_out_sk_spl                   false
% 2.22/1.02  --abstr_cl_out                          false
% 2.22/1.02  
% 2.22/1.02  ------ Global Options
% 2.22/1.02  
% 2.22/1.02  --schedule                              default
% 2.22/1.02  --add_important_lit                     false
% 2.22/1.02  --prop_solver_per_cl                    1000
% 2.22/1.02  --min_unsat_core                        false
% 2.22/1.02  --soft_assumptions                      false
% 2.22/1.02  --soft_lemma_size                       3
% 2.22/1.02  --prop_impl_unit_size                   0
% 2.22/1.02  --prop_impl_unit                        []
% 2.22/1.02  --share_sel_clauses                     true
% 2.22/1.02  --reset_solvers                         false
% 2.22/1.02  --bc_imp_inh                            [conj_cone]
% 2.22/1.02  --conj_cone_tolerance                   3.
% 2.22/1.02  --extra_neg_conj                        none
% 2.22/1.02  --large_theory_mode                     true
% 2.22/1.02  --prolific_symb_bound                   200
% 2.22/1.02  --lt_threshold                          2000
% 2.22/1.02  --clause_weak_htbl                      true
% 2.22/1.02  --gc_record_bc_elim                     false
% 2.22/1.02  
% 2.22/1.02  ------ Preprocessing Options
% 2.22/1.02  
% 2.22/1.02  --preprocessing_flag                    true
% 2.22/1.02  --time_out_prep_mult                    0.1
% 2.22/1.02  --splitting_mode                        input
% 2.22/1.02  --splitting_grd                         true
% 2.22/1.02  --splitting_cvd                         false
% 2.22/1.02  --splitting_cvd_svl                     false
% 2.22/1.02  --splitting_nvd                         32
% 2.22/1.02  --sub_typing                            true
% 2.22/1.02  --prep_gs_sim                           true
% 2.22/1.02  --prep_unflatten                        true
% 2.22/1.02  --prep_res_sim                          true
% 2.22/1.02  --prep_upred                            true
% 2.22/1.02  --prep_sem_filter                       exhaustive
% 2.22/1.02  --prep_sem_filter_out                   false
% 2.22/1.02  --pred_elim                             true
% 2.22/1.02  --res_sim_input                         true
% 2.22/1.02  --eq_ax_congr_red                       true
% 2.22/1.02  --pure_diseq_elim                       true
% 2.22/1.02  --brand_transform                       false
% 2.22/1.02  --non_eq_to_eq                          false
% 2.22/1.02  --prep_def_merge                        true
% 2.22/1.02  --prep_def_merge_prop_impl              false
% 2.22/1.02  --prep_def_merge_mbd                    true
% 2.22/1.02  --prep_def_merge_tr_red                 false
% 2.22/1.02  --prep_def_merge_tr_cl                  false
% 2.22/1.02  --smt_preprocessing                     true
% 2.22/1.02  --smt_ac_axioms                         fast
% 2.22/1.02  --preprocessed_out                      false
% 2.22/1.02  --preprocessed_stats                    false
% 2.22/1.02  
% 2.22/1.02  ------ Abstraction refinement Options
% 2.22/1.02  
% 2.22/1.02  --abstr_ref                             []
% 2.22/1.02  --abstr_ref_prep                        false
% 2.22/1.02  --abstr_ref_until_sat                   false
% 2.22/1.02  --abstr_ref_sig_restrict                funpre
% 2.22/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/1.02  --abstr_ref_under                       []
% 2.22/1.02  
% 2.22/1.02  ------ SAT Options
% 2.22/1.02  
% 2.22/1.02  --sat_mode                              false
% 2.22/1.02  --sat_fm_restart_options                ""
% 2.22/1.02  --sat_gr_def                            false
% 2.22/1.02  --sat_epr_types                         true
% 2.22/1.02  --sat_non_cyclic_types                  false
% 2.22/1.02  --sat_finite_models                     false
% 2.22/1.02  --sat_fm_lemmas                         false
% 2.22/1.02  --sat_fm_prep                           false
% 2.22/1.02  --sat_fm_uc_incr                        true
% 2.22/1.02  --sat_out_model                         small
% 2.22/1.02  --sat_out_clauses                       false
% 2.22/1.02  
% 2.22/1.02  ------ QBF Options
% 2.22/1.02  
% 2.22/1.02  --qbf_mode                              false
% 2.22/1.02  --qbf_elim_univ                         false
% 2.22/1.02  --qbf_dom_inst                          none
% 2.22/1.02  --qbf_dom_pre_inst                      false
% 2.22/1.02  --qbf_sk_in                             false
% 2.22/1.02  --qbf_pred_elim                         true
% 2.22/1.02  --qbf_split                             512
% 2.22/1.02  
% 2.22/1.02  ------ BMC1 Options
% 2.22/1.02  
% 2.22/1.02  --bmc1_incremental                      false
% 2.22/1.02  --bmc1_axioms                           reachable_all
% 2.22/1.02  --bmc1_min_bound                        0
% 2.22/1.02  --bmc1_max_bound                        -1
% 2.22/1.02  --bmc1_max_bound_default                -1
% 2.22/1.02  --bmc1_symbol_reachability              true
% 2.22/1.02  --bmc1_property_lemmas                  false
% 2.22/1.02  --bmc1_k_induction                      false
% 2.22/1.02  --bmc1_non_equiv_states                 false
% 2.22/1.02  --bmc1_deadlock                         false
% 2.22/1.02  --bmc1_ucm                              false
% 2.22/1.02  --bmc1_add_unsat_core                   none
% 2.22/1.02  --bmc1_unsat_core_children              false
% 2.22/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/1.02  --bmc1_out_stat                         full
% 2.22/1.02  --bmc1_ground_init                      false
% 2.22/1.02  --bmc1_pre_inst_next_state              false
% 2.22/1.02  --bmc1_pre_inst_state                   false
% 2.22/1.02  --bmc1_pre_inst_reach_state             false
% 2.22/1.02  --bmc1_out_unsat_core                   false
% 2.22/1.02  --bmc1_aig_witness_out                  false
% 2.22/1.02  --bmc1_verbose                          false
% 2.22/1.02  --bmc1_dump_clauses_tptp                false
% 2.22/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.22/1.02  --bmc1_dump_file                        -
% 2.22/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.22/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.22/1.02  --bmc1_ucm_extend_mode                  1
% 2.22/1.02  --bmc1_ucm_init_mode                    2
% 2.22/1.02  --bmc1_ucm_cone_mode                    none
% 2.22/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.22/1.02  --bmc1_ucm_relax_model                  4
% 2.22/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.22/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/1.02  --bmc1_ucm_layered_model                none
% 2.22/1.02  --bmc1_ucm_max_lemma_size               10
% 2.22/1.02  
% 2.22/1.02  ------ AIG Options
% 2.22/1.02  
% 2.22/1.02  --aig_mode                              false
% 2.22/1.02  
% 2.22/1.02  ------ Instantiation Options
% 2.22/1.02  
% 2.22/1.02  --instantiation_flag                    true
% 2.22/1.02  --inst_sos_flag                         false
% 2.22/1.02  --inst_sos_phase                        true
% 2.22/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/1.02  --inst_lit_sel_side                     num_symb
% 2.22/1.02  --inst_solver_per_active                1400
% 2.22/1.02  --inst_solver_calls_frac                1.
% 2.22/1.02  --inst_passive_queue_type               priority_queues
% 2.22/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/1.02  --inst_passive_queues_freq              [25;2]
% 2.22/1.02  --inst_dismatching                      true
% 2.22/1.02  --inst_eager_unprocessed_to_passive     true
% 2.22/1.02  --inst_prop_sim_given                   true
% 2.22/1.02  --inst_prop_sim_new                     false
% 2.22/1.02  --inst_subs_new                         false
% 2.22/1.02  --inst_eq_res_simp                      false
% 2.22/1.02  --inst_subs_given                       false
% 2.22/1.02  --inst_orphan_elimination               true
% 2.22/1.02  --inst_learning_loop_flag               true
% 2.22/1.02  --inst_learning_start                   3000
% 2.22/1.02  --inst_learning_factor                  2
% 2.22/1.02  --inst_start_prop_sim_after_learn       3
% 2.22/1.02  --inst_sel_renew                        solver
% 2.22/1.02  --inst_lit_activity_flag                true
% 2.22/1.02  --inst_restr_to_given                   false
% 2.22/1.02  --inst_activity_threshold               500
% 2.22/1.02  --inst_out_proof                        true
% 2.22/1.02  
% 2.22/1.02  ------ Resolution Options
% 2.22/1.02  
% 2.22/1.02  --resolution_flag                       true
% 2.22/1.02  --res_lit_sel                           adaptive
% 2.22/1.02  --res_lit_sel_side                      none
% 2.22/1.02  --res_ordering                          kbo
% 2.22/1.02  --res_to_prop_solver                    active
% 2.22/1.02  --res_prop_simpl_new                    false
% 2.22/1.02  --res_prop_simpl_given                  true
% 2.22/1.02  --res_passive_queue_type                priority_queues
% 2.22/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/1.02  --res_passive_queues_freq               [15;5]
% 2.22/1.02  --res_forward_subs                      full
% 2.22/1.02  --res_backward_subs                     full
% 2.22/1.02  --res_forward_subs_resolution           true
% 2.22/1.02  --res_backward_subs_resolution          true
% 2.22/1.02  --res_orphan_elimination                true
% 2.22/1.02  --res_time_limit                        2.
% 2.22/1.02  --res_out_proof                         true
% 2.22/1.02  
% 2.22/1.02  ------ Superposition Options
% 2.22/1.02  
% 2.22/1.02  --superposition_flag                    true
% 2.22/1.02  --sup_passive_queue_type                priority_queues
% 2.22/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.22/1.02  --demod_completeness_check              fast
% 2.22/1.02  --demod_use_ground                      true
% 2.22/1.02  --sup_to_prop_solver                    passive
% 2.22/1.02  --sup_prop_simpl_new                    true
% 2.22/1.02  --sup_prop_simpl_given                  true
% 2.22/1.02  --sup_fun_splitting                     false
% 2.22/1.02  --sup_smt_interval                      50000
% 2.22/1.02  
% 2.22/1.02  ------ Superposition Simplification Setup
% 2.22/1.02  
% 2.22/1.02  --sup_indices_passive                   []
% 2.22/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_full_bw                           [BwDemod]
% 2.22/1.02  --sup_immed_triv                        [TrivRules]
% 2.22/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_immed_bw_main                     []
% 2.22/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.02  
% 2.22/1.02  ------ Combination Options
% 2.22/1.02  
% 2.22/1.02  --comb_res_mult                         3
% 2.22/1.02  --comb_sup_mult                         2
% 2.22/1.02  --comb_inst_mult                        10
% 2.22/1.02  
% 2.22/1.02  ------ Debug Options
% 2.22/1.02  
% 2.22/1.02  --dbg_backtrace                         false
% 2.22/1.02  --dbg_dump_prop_clauses                 false
% 2.22/1.02  --dbg_dump_prop_clauses_file            -
% 2.22/1.02  --dbg_out_stat                          false
% 2.22/1.02  ------ Parsing...
% 2.22/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.22/1.02  
% 2.22/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.22/1.02  
% 2.22/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.22/1.02  
% 2.22/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.22/1.02  ------ Proving...
% 2.22/1.02  ------ Problem Properties 
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  clauses                                 33
% 2.22/1.02  conjectures                             20
% 2.22/1.02  EPR                                     16
% 2.22/1.02  Horn                                    27
% 2.22/1.02  unary                                   18
% 2.22/1.02  binary                                  5
% 2.22/1.02  lits                                    126
% 2.22/1.02  lits eq                                 13
% 2.22/1.02  fd_pure                                 0
% 2.22/1.02  fd_pseudo                               0
% 2.22/1.02  fd_cond                                 0
% 2.22/1.02  fd_pseudo_cond                          0
% 2.22/1.02  AC symbols                              0
% 2.22/1.02  
% 2.22/1.02  ------ Schedule dynamic 5 is on 
% 2.22/1.02  
% 2.22/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  ------ 
% 2.22/1.02  Current options:
% 2.22/1.02  ------ 
% 2.22/1.02  
% 2.22/1.02  ------ Input Options
% 2.22/1.02  
% 2.22/1.02  --out_options                           all
% 2.22/1.02  --tptp_safe_out                         true
% 2.22/1.02  --problem_path                          ""
% 2.22/1.02  --include_path                          ""
% 2.22/1.02  --clausifier                            res/vclausify_rel
% 2.22/1.02  --clausifier_options                    --mode clausify
% 2.22/1.02  --stdin                                 false
% 2.22/1.02  --stats_out                             all
% 2.22/1.02  
% 2.22/1.02  ------ General Options
% 2.22/1.02  
% 2.22/1.02  --fof                                   false
% 2.22/1.02  --time_out_real                         305.
% 2.22/1.02  --time_out_virtual                      -1.
% 2.22/1.02  --symbol_type_check                     false
% 2.22/1.02  --clausify_out                          false
% 2.22/1.02  --sig_cnt_out                           false
% 2.22/1.02  --trig_cnt_out                          false
% 2.22/1.02  --trig_cnt_out_tolerance                1.
% 2.22/1.02  --trig_cnt_out_sk_spl                   false
% 2.22/1.02  --abstr_cl_out                          false
% 2.22/1.02  
% 2.22/1.02  ------ Global Options
% 2.22/1.02  
% 2.22/1.02  --schedule                              default
% 2.22/1.02  --add_important_lit                     false
% 2.22/1.02  --prop_solver_per_cl                    1000
% 2.22/1.02  --min_unsat_core                        false
% 2.22/1.02  --soft_assumptions                      false
% 2.22/1.02  --soft_lemma_size                       3
% 2.22/1.02  --prop_impl_unit_size                   0
% 2.22/1.02  --prop_impl_unit                        []
% 2.22/1.02  --share_sel_clauses                     true
% 2.22/1.02  --reset_solvers                         false
% 2.22/1.02  --bc_imp_inh                            [conj_cone]
% 2.22/1.02  --conj_cone_tolerance                   3.
% 2.22/1.02  --extra_neg_conj                        none
% 2.22/1.02  --large_theory_mode                     true
% 2.22/1.02  --prolific_symb_bound                   200
% 2.22/1.02  --lt_threshold                          2000
% 2.22/1.02  --clause_weak_htbl                      true
% 2.22/1.02  --gc_record_bc_elim                     false
% 2.22/1.02  
% 2.22/1.02  ------ Preprocessing Options
% 2.22/1.02  
% 2.22/1.02  --preprocessing_flag                    true
% 2.22/1.02  --time_out_prep_mult                    0.1
% 2.22/1.02  --splitting_mode                        input
% 2.22/1.02  --splitting_grd                         true
% 2.22/1.02  --splitting_cvd                         false
% 2.22/1.02  --splitting_cvd_svl                     false
% 2.22/1.02  --splitting_nvd                         32
% 2.22/1.02  --sub_typing                            true
% 2.22/1.02  --prep_gs_sim                           true
% 2.22/1.02  --prep_unflatten                        true
% 2.22/1.02  --prep_res_sim                          true
% 2.22/1.02  --prep_upred                            true
% 2.22/1.02  --prep_sem_filter                       exhaustive
% 2.22/1.02  --prep_sem_filter_out                   false
% 2.22/1.02  --pred_elim                             true
% 2.22/1.02  --res_sim_input                         true
% 2.22/1.02  --eq_ax_congr_red                       true
% 2.22/1.02  --pure_diseq_elim                       true
% 2.22/1.02  --brand_transform                       false
% 2.22/1.02  --non_eq_to_eq                          false
% 2.22/1.02  --prep_def_merge                        true
% 2.22/1.02  --prep_def_merge_prop_impl              false
% 2.22/1.02  --prep_def_merge_mbd                    true
% 2.22/1.02  --prep_def_merge_tr_red                 false
% 2.22/1.02  --prep_def_merge_tr_cl                  false
% 2.22/1.02  --smt_preprocessing                     true
% 2.22/1.02  --smt_ac_axioms                         fast
% 2.22/1.02  --preprocessed_out                      false
% 2.22/1.02  --preprocessed_stats                    false
% 2.22/1.02  
% 2.22/1.02  ------ Abstraction refinement Options
% 2.22/1.02  
% 2.22/1.02  --abstr_ref                             []
% 2.22/1.02  --abstr_ref_prep                        false
% 2.22/1.02  --abstr_ref_until_sat                   false
% 2.22/1.02  --abstr_ref_sig_restrict                funpre
% 2.22/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/1.02  --abstr_ref_under                       []
% 2.22/1.02  
% 2.22/1.02  ------ SAT Options
% 2.22/1.02  
% 2.22/1.02  --sat_mode                              false
% 2.22/1.02  --sat_fm_restart_options                ""
% 2.22/1.02  --sat_gr_def                            false
% 2.22/1.02  --sat_epr_types                         true
% 2.22/1.02  --sat_non_cyclic_types                  false
% 2.22/1.02  --sat_finite_models                     false
% 2.22/1.02  --sat_fm_lemmas                         false
% 2.22/1.02  --sat_fm_prep                           false
% 2.22/1.02  --sat_fm_uc_incr                        true
% 2.22/1.02  --sat_out_model                         small
% 2.22/1.02  --sat_out_clauses                       false
% 2.22/1.02  
% 2.22/1.02  ------ QBF Options
% 2.22/1.02  
% 2.22/1.02  --qbf_mode                              false
% 2.22/1.02  --qbf_elim_univ                         false
% 2.22/1.02  --qbf_dom_inst                          none
% 2.22/1.02  --qbf_dom_pre_inst                      false
% 2.22/1.02  --qbf_sk_in                             false
% 2.22/1.02  --qbf_pred_elim                         true
% 2.22/1.02  --qbf_split                             512
% 2.22/1.02  
% 2.22/1.02  ------ BMC1 Options
% 2.22/1.02  
% 2.22/1.02  --bmc1_incremental                      false
% 2.22/1.02  --bmc1_axioms                           reachable_all
% 2.22/1.02  --bmc1_min_bound                        0
% 2.22/1.02  --bmc1_max_bound                        -1
% 2.22/1.02  --bmc1_max_bound_default                -1
% 2.22/1.02  --bmc1_symbol_reachability              true
% 2.22/1.02  --bmc1_property_lemmas                  false
% 2.22/1.02  --bmc1_k_induction                      false
% 2.22/1.02  --bmc1_non_equiv_states                 false
% 2.22/1.02  --bmc1_deadlock                         false
% 2.22/1.02  --bmc1_ucm                              false
% 2.22/1.02  --bmc1_add_unsat_core                   none
% 2.22/1.02  --bmc1_unsat_core_children              false
% 2.22/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/1.02  --bmc1_out_stat                         full
% 2.22/1.02  --bmc1_ground_init                      false
% 2.22/1.02  --bmc1_pre_inst_next_state              false
% 2.22/1.02  --bmc1_pre_inst_state                   false
% 2.22/1.02  --bmc1_pre_inst_reach_state             false
% 2.22/1.02  --bmc1_out_unsat_core                   false
% 2.22/1.02  --bmc1_aig_witness_out                  false
% 2.22/1.02  --bmc1_verbose                          false
% 2.22/1.02  --bmc1_dump_clauses_tptp                false
% 2.22/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.22/1.02  --bmc1_dump_file                        -
% 2.22/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.22/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.22/1.02  --bmc1_ucm_extend_mode                  1
% 2.22/1.02  --bmc1_ucm_init_mode                    2
% 2.22/1.02  --bmc1_ucm_cone_mode                    none
% 2.22/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.22/1.02  --bmc1_ucm_relax_model                  4
% 2.22/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.22/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/1.02  --bmc1_ucm_layered_model                none
% 2.22/1.02  --bmc1_ucm_max_lemma_size               10
% 2.22/1.02  
% 2.22/1.02  ------ AIG Options
% 2.22/1.02  
% 2.22/1.02  --aig_mode                              false
% 2.22/1.02  
% 2.22/1.02  ------ Instantiation Options
% 2.22/1.02  
% 2.22/1.02  --instantiation_flag                    true
% 2.22/1.02  --inst_sos_flag                         false
% 2.22/1.02  --inst_sos_phase                        true
% 2.22/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/1.02  --inst_lit_sel_side                     none
% 2.22/1.02  --inst_solver_per_active                1400
% 2.22/1.02  --inst_solver_calls_frac                1.
% 2.22/1.02  --inst_passive_queue_type               priority_queues
% 2.22/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/1.02  --inst_passive_queues_freq              [25;2]
% 2.22/1.02  --inst_dismatching                      true
% 2.22/1.02  --inst_eager_unprocessed_to_passive     true
% 2.22/1.02  --inst_prop_sim_given                   true
% 2.22/1.02  --inst_prop_sim_new                     false
% 2.22/1.02  --inst_subs_new                         false
% 2.22/1.02  --inst_eq_res_simp                      false
% 2.22/1.02  --inst_subs_given                       false
% 2.22/1.02  --inst_orphan_elimination               true
% 2.22/1.02  --inst_learning_loop_flag               true
% 2.22/1.02  --inst_learning_start                   3000
% 2.22/1.02  --inst_learning_factor                  2
% 2.22/1.02  --inst_start_prop_sim_after_learn       3
% 2.22/1.02  --inst_sel_renew                        solver
% 2.22/1.02  --inst_lit_activity_flag                true
% 2.22/1.02  --inst_restr_to_given                   false
% 2.22/1.02  --inst_activity_threshold               500
% 2.22/1.02  --inst_out_proof                        true
% 2.22/1.02  
% 2.22/1.02  ------ Resolution Options
% 2.22/1.02  
% 2.22/1.02  --resolution_flag                       false
% 2.22/1.02  --res_lit_sel                           adaptive
% 2.22/1.02  --res_lit_sel_side                      none
% 2.22/1.02  --res_ordering                          kbo
% 2.22/1.02  --res_to_prop_solver                    active
% 2.22/1.02  --res_prop_simpl_new                    false
% 2.22/1.02  --res_prop_simpl_given                  true
% 2.22/1.02  --res_passive_queue_type                priority_queues
% 2.22/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/1.02  --res_passive_queues_freq               [15;5]
% 2.22/1.02  --res_forward_subs                      full
% 2.22/1.02  --res_backward_subs                     full
% 2.22/1.02  --res_forward_subs_resolution           true
% 2.22/1.02  --res_backward_subs_resolution          true
% 2.22/1.02  --res_orphan_elimination                true
% 2.22/1.02  --res_time_limit                        2.
% 2.22/1.02  --res_out_proof                         true
% 2.22/1.02  
% 2.22/1.02  ------ Superposition Options
% 2.22/1.02  
% 2.22/1.02  --superposition_flag                    true
% 2.22/1.02  --sup_passive_queue_type                priority_queues
% 2.22/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.22/1.02  --demod_completeness_check              fast
% 2.22/1.02  --demod_use_ground                      true
% 2.22/1.02  --sup_to_prop_solver                    passive
% 2.22/1.02  --sup_prop_simpl_new                    true
% 2.22/1.02  --sup_prop_simpl_given                  true
% 2.22/1.02  --sup_fun_splitting                     false
% 2.22/1.02  --sup_smt_interval                      50000
% 2.22/1.02  
% 2.22/1.02  ------ Superposition Simplification Setup
% 2.22/1.02  
% 2.22/1.02  --sup_indices_passive                   []
% 2.22/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_full_bw                           [BwDemod]
% 2.22/1.02  --sup_immed_triv                        [TrivRules]
% 2.22/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_immed_bw_main                     []
% 2.22/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.02  
% 2.22/1.02  ------ Combination Options
% 2.22/1.02  
% 2.22/1.02  --comb_res_mult                         3
% 2.22/1.02  --comb_sup_mult                         2
% 2.22/1.02  --comb_inst_mult                        10
% 2.22/1.02  
% 2.22/1.02  ------ Debug Options
% 2.22/1.02  
% 2.22/1.02  --dbg_backtrace                         false
% 2.22/1.02  --dbg_dump_prop_clauses                 false
% 2.22/1.02  --dbg_dump_prop_clauses_file            -
% 2.22/1.02  --dbg_out_stat                          false
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  ------ Proving...
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  % SZS status Theorem for theBenchmark.p
% 2.22/1.02  
% 2.22/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.22/1.02  
% 2.22/1.02  fof(f11,axiom,(
% 2.22/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f30,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/1.02    inference(ennf_transformation,[],[f11])).
% 2.22/1.02  
% 2.22/1.02  fof(f31,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/1.02    inference(flattening,[],[f30])).
% 2.22/1.02  
% 2.22/1.02  fof(f35,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/1.02    inference(nnf_transformation,[],[f31])).
% 2.22/1.02  
% 2.22/1.02  fof(f59,plain,(
% 2.22/1.02    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f35])).
% 2.22/1.02  
% 2.22/1.02  fof(f85,plain,(
% 2.22/1.02    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/1.02    inference(equality_resolution,[],[f59])).
% 2.22/1.02  
% 2.22/1.02  fof(f12,conjecture,(
% 2.22/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f13,negated_conjecture,(
% 2.22/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 2.22/1.02    inference(negated_conjecture,[],[f12])).
% 2.22/1.02  
% 2.22/1.02  fof(f32,plain,(
% 2.22/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.22/1.02    inference(ennf_transformation,[],[f13])).
% 2.22/1.02  
% 2.22/1.02  fof(f33,plain,(
% 2.22/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/1.02    inference(flattening,[],[f32])).
% 2.22/1.02  
% 2.22/1.02  fof(f36,plain,(
% 2.22/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/1.02    inference(nnf_transformation,[],[f33])).
% 2.22/1.02  
% 2.22/1.02  fof(f37,plain,(
% 2.22/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/1.02    inference(flattening,[],[f36])).
% 2.22/1.02  
% 2.22/1.02  fof(f45,plain,(
% 2.22/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | r1_tmap_1(X3,X0,X4,X6)) & sK7 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 2.22/1.02    introduced(choice_axiom,[])).
% 2.22/1.02  
% 2.22/1.02  fof(f44,plain,(
% 2.22/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,sK6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,sK6)) & sK6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.22/1.02    introduced(choice_axiom,[])).
% 2.22/1.02  
% 2.22/1.02  fof(f43,plain,(
% 2.22/1.02    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(X2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 2.22/1.02    introduced(choice_axiom,[])).
% 2.22/1.02  
% 2.22/1.02  fof(f42,plain,(
% 2.22/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7) | ~r1_tmap_1(X3,X0,sK4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7) | r1_tmap_1(X3,X0,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 2.22/1.02    introduced(choice_axiom,[])).
% 2.22/1.02  
% 2.22/1.02  fof(f41,plain,(
% 2.22/1.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7) | ~r1_tmap_1(sK3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7) | r1_tmap_1(sK3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 2.22/1.02    introduced(choice_axiom,[])).
% 2.22/1.02  
% 2.22/1.02  fof(f40,plain,(
% 2.22/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 2.22/1.02    introduced(choice_axiom,[])).
% 2.22/1.02  
% 2.22/1.02  fof(f39,plain,(
% 2.22/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.22/1.02    introduced(choice_axiom,[])).
% 2.22/1.02  
% 2.22/1.02  fof(f38,plain,(
% 2.22/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.22/1.02    introduced(choice_axiom,[])).
% 2.22/1.02  
% 2.22/1.02  fof(f46,plain,(
% 2.22/1.02    ((((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.22/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f37,f45,f44,f43,f42,f41,f40,f39,f38])).
% 2.22/1.02  
% 2.22/1.02  fof(f78,plain,(
% 2.22/1.02    r2_hidden(sK6,sK5)),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f2,axiom,(
% 2.22/1.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f14,plain,(
% 2.22/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.22/1.02    inference(ennf_transformation,[],[f2])).
% 2.22/1.02  
% 2.22/1.02  fof(f15,plain,(
% 2.22/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.22/1.02    inference(flattening,[],[f14])).
% 2.22/1.02  
% 2.22/1.02  fof(f49,plain,(
% 2.22/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f15])).
% 2.22/1.02  
% 2.22/1.02  fof(f10,axiom,(
% 2.22/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f28,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.22/1.02    inference(ennf_transformation,[],[f10])).
% 2.22/1.02  
% 2.22/1.02  fof(f29,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.22/1.02    inference(flattening,[],[f28])).
% 2.22/1.02  
% 2.22/1.02  fof(f57,plain,(
% 2.22/1.02    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f29])).
% 2.22/1.02  
% 2.22/1.02  fof(f71,plain,(
% 2.22/1.02    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f70,plain,(
% 2.22/1.02    v1_funct_1(sK4)),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f9,axiom,(
% 2.22/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f26,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/1.02    inference(ennf_transformation,[],[f9])).
% 2.22/1.02  
% 2.22/1.02  fof(f27,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/1.02    inference(flattening,[],[f26])).
% 2.22/1.02  
% 2.22/1.02  fof(f56,plain,(
% 2.22/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f27])).
% 2.22/1.02  
% 2.22/1.02  fof(f84,plain,(
% 2.22/1.02    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/1.02    inference(equality_resolution,[],[f56])).
% 2.22/1.02  
% 2.22/1.02  fof(f7,axiom,(
% 2.22/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f22,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/1.02    inference(ennf_transformation,[],[f7])).
% 2.22/1.02  
% 2.22/1.02  fof(f23,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/1.02    inference(flattening,[],[f22])).
% 2.22/1.02  
% 2.22/1.02  fof(f54,plain,(
% 2.22/1.02    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f23])).
% 2.22/1.02  
% 2.22/1.02  fof(f8,axiom,(
% 2.22/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f24,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/1.02    inference(ennf_transformation,[],[f8])).
% 2.22/1.02  
% 2.22/1.02  fof(f25,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/1.02    inference(flattening,[],[f24])).
% 2.22/1.02  
% 2.22/1.02  fof(f55,plain,(
% 2.22/1.02    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f25])).
% 2.22/1.02  
% 2.22/1.02  fof(f69,plain,(
% 2.22/1.02    m1_pre_topc(sK3,sK1)),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f3,axiom,(
% 2.22/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f16,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.22/1.02    inference(ennf_transformation,[],[f3])).
% 2.22/1.02  
% 2.22/1.02  fof(f17,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.22/1.02    inference(flattening,[],[f16])).
% 2.22/1.02  
% 2.22/1.02  fof(f50,plain,(
% 2.22/1.02    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f17])).
% 2.22/1.02  
% 2.22/1.02  fof(f4,axiom,(
% 2.22/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f18,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.02    inference(ennf_transformation,[],[f4])).
% 2.22/1.02  
% 2.22/1.02  fof(f51,plain,(
% 2.22/1.02    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f18])).
% 2.22/1.02  
% 2.22/1.02  fof(f5,axiom,(
% 2.22/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f19,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.02    inference(ennf_transformation,[],[f5])).
% 2.22/1.02  
% 2.22/1.02  fof(f52,plain,(
% 2.22/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f19])).
% 2.22/1.02  
% 2.22/1.02  fof(f6,axiom,(
% 2.22/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f20,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/1.02    inference(ennf_transformation,[],[f6])).
% 2.22/1.02  
% 2.22/1.02  fof(f21,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/1.02    inference(flattening,[],[f20])).
% 2.22/1.02  
% 2.22/1.02  fof(f53,plain,(
% 2.22/1.02    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f21])).
% 2.22/1.02  
% 2.22/1.02  fof(f83,plain,(
% 2.22/1.02    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.22/1.02    inference(equality_resolution,[],[f53])).
% 2.22/1.02  
% 2.22/1.02  fof(f80,plain,(
% 2.22/1.02    sK6 = sK7),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f1,axiom,(
% 2.22/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f34,plain,(
% 2.22/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.22/1.02    inference(nnf_transformation,[],[f1])).
% 2.22/1.02  
% 2.22/1.02  fof(f48,plain,(
% 2.22/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f34])).
% 2.22/1.02  
% 2.22/1.02  fof(f79,plain,(
% 2.22/1.02    r1_tarski(sK5,u1_struct_0(sK2))),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f82,plain,(
% 2.22/1.02    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f81,plain,(
% 2.22/1.02    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f77,plain,(
% 2.22/1.02    v3_pre_topc(sK5,sK1)),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f75,plain,(
% 2.22/1.02    m1_subset_1(sK6,u1_struct_0(sK3))),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f74,plain,(
% 2.22/1.02    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f73,plain,(
% 2.22/1.02    m1_pre_topc(sK2,sK3)),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f72,plain,(
% 2.22/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f68,plain,(
% 2.22/1.02    ~v2_struct_0(sK3)),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f66,plain,(
% 2.22/1.02    ~v2_struct_0(sK2)),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f65,plain,(
% 2.22/1.02    l1_pre_topc(sK1)),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f64,plain,(
% 2.22/1.02    v2_pre_topc(sK1)),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f63,plain,(
% 2.22/1.02    ~v2_struct_0(sK1)),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f62,plain,(
% 2.22/1.02    l1_pre_topc(sK0)),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f61,plain,(
% 2.22/1.02    v2_pre_topc(sK0)),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  fof(f60,plain,(
% 2.22/1.02    ~v2_struct_0(sK0)),
% 2.22/1.02    inference(cnf_transformation,[],[f46])).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1773,plain,
% 2.22/1.02      ( ~ r1_tmap_1(X0_53,X1_53,X0_54,X1_54)
% 2.22/1.02      | r1_tmap_1(X0_53,X1_53,X2_54,X3_54)
% 2.22/1.02      | X2_54 != X0_54
% 2.22/1.02      | X3_54 != X1_54 ),
% 2.22/1.02      theory(equality) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_3345,plain,
% 2.22/1.02      ( r1_tmap_1(sK2,sK0,X0_54,X1_54)
% 2.22/1.02      | ~ r1_tmap_1(sK2,sK0,X2_54,sK6)
% 2.22/1.02      | X0_54 != X2_54
% 2.22/1.02      | X1_54 != sK6 ),
% 2.22/1.02      inference(instantiation,[status(thm)],[c_1773]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_3722,plain,
% 2.22/1.02      ( ~ r1_tmap_1(sK2,sK0,X0_54,sK6)
% 2.22/1.02      | r1_tmap_1(sK2,sK0,X1_54,sK7)
% 2.22/1.02      | X1_54 != X0_54
% 2.22/1.02      | sK7 != sK6 ),
% 2.22/1.02      inference(instantiation,[status(thm)],[c_3345]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_4576,plain,
% 2.22/1.02      ( r1_tmap_1(sK2,sK0,X0_54,sK7)
% 2.22/1.02      | ~ r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK6)
% 2.22/1.02      | X0_54 != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
% 2.22/1.02      | sK7 != sK6 ),
% 2.22/1.02      inference(instantiation,[status(thm)],[c_3722]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_5062,plain,
% 2.22/1.02      ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 2.22/1.02      | ~ r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK6)
% 2.22/1.02      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
% 2.22/1.02      | sK7 != sK6 ),
% 2.22/1.02      inference(instantiation,[status(thm)],[c_4576]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_3719,plain,
% 2.22/1.02      ( ~ r1_tmap_1(sK2,sK0,X0_54,sK6)
% 2.22/1.02      | r1_tmap_1(sK2,sK0,X1_54,sK6)
% 2.22/1.02      | X1_54 != X0_54
% 2.22/1.02      | sK6 != sK6 ),
% 2.22/1.02      inference(instantiation,[status(thm)],[c_3345]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_4193,plain,
% 2.22/1.02      ( r1_tmap_1(sK2,sK0,X0_54,sK6)
% 2.22/1.02      | ~ r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
% 2.22/1.02      | X0_54 != k2_tmap_1(sK3,sK0,sK4,sK2)
% 2.22/1.02      | sK6 != sK6 ),
% 2.22/1.02      inference(instantiation,[status(thm)],[c_3719]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_5029,plain,
% 2.22/1.02      ( r1_tmap_1(sK2,sK0,k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)),sK6)
% 2.22/1.02      | ~ r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
% 2.22/1.02      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) != k2_tmap_1(sK3,sK0,sK4,sK2)
% 2.22/1.02      | sK6 != sK6 ),
% 2.22/1.02      inference(instantiation,[status(thm)],[c_4193]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1763,plain,
% 2.22/1.02      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 2.22/1.02      theory(equality) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_3807,plain,
% 2.22/1.02      ( X0_54 != X1_54
% 2.22/1.02      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != X1_54
% 2.22/1.02      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = X0_54 ),
% 2.22/1.02      inference(instantiation,[status(thm)],[c_1763]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_4124,plain,
% 2.22/1.02      ( X0_54 != k3_tmap_1(sK1,sK0,sK3,sK2,X1_54)
% 2.22/1.02      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = X0_54
% 2.22/1.02      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,X1_54) ),
% 2.22/1.02      inference(instantiation,[status(thm)],[c_3807]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_4527,plain,
% 2.22/1.02      ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 2.22/1.02      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
% 2.22/1.02      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
% 2.22/1.02      inference(instantiation,[status(thm)],[c_4124]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_11,plain,
% 2.22/1.02      ( r1_tmap_1(X0,X1,X2,X3)
% 2.22/1.02      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.22/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.22/1.02      | ~ v3_pre_topc(X6,X0)
% 2.22/1.02      | ~ m1_pre_topc(X4,X5)
% 2.22/1.02      | ~ m1_pre_topc(X0,X5)
% 2.22/1.02      | ~ m1_pre_topc(X4,X0)
% 2.22/1.02      | ~ r2_hidden(X3,X6)
% 2.22/1.02      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.22/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.22/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.22/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.22/1.02      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.22/1.02      | v2_struct_0(X5)
% 2.22/1.02      | v2_struct_0(X1)
% 2.22/1.02      | v2_struct_0(X4)
% 2.22/1.02      | v2_struct_0(X0)
% 2.22/1.02      | ~ v1_funct_1(X2)
% 2.22/1.02      | ~ l1_pre_topc(X5)
% 2.22/1.02      | ~ l1_pre_topc(X1)
% 2.22/1.02      | ~ v2_pre_topc(X5)
% 2.22/1.02      | ~ v2_pre_topc(X1) ),
% 2.22/1.02      inference(cnf_transformation,[],[f85]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_17,negated_conjecture,
% 2.22/1.02      ( r2_hidden(sK6,sK5) ),
% 2.22/1.02      inference(cnf_transformation,[],[f78]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_533,plain,
% 2.22/1.02      ( r1_tmap_1(X0,X1,X2,X3)
% 2.22/1.02      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.22/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.22/1.02      | ~ v3_pre_topc(X6,X0)
% 2.22/1.02      | ~ m1_pre_topc(X4,X0)
% 2.22/1.02      | ~ m1_pre_topc(X4,X5)
% 2.22/1.02      | ~ m1_pre_topc(X0,X5)
% 2.22/1.02      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.22/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.22/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.22/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.22/1.02      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.22/1.02      | v2_struct_0(X0)
% 2.22/1.02      | v2_struct_0(X1)
% 2.22/1.02      | v2_struct_0(X4)
% 2.22/1.02      | v2_struct_0(X5)
% 2.22/1.02      | ~ v1_funct_1(X2)
% 2.22/1.02      | ~ l1_pre_topc(X1)
% 2.22/1.02      | ~ l1_pre_topc(X5)
% 2.22/1.02      | ~ v2_pre_topc(X1)
% 2.22/1.02      | ~ v2_pre_topc(X5)
% 2.22/1.02      | sK5 != X6
% 2.22/1.02      | sK6 != X3 ),
% 2.22/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_534,plain,
% 2.22/1.02      ( r1_tmap_1(X0,X1,X2,sK6)
% 2.22/1.02      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
% 2.22/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.22/1.02      | ~ v3_pre_topc(sK5,X0)
% 2.22/1.02      | ~ m1_pre_topc(X3,X0)
% 2.22/1.02      | ~ m1_pre_topc(X3,X4)
% 2.22/1.02      | ~ m1_pre_topc(X0,X4)
% 2.22/1.02      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 2.22/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.22/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.22/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.22/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.22/1.02      | v2_struct_0(X0)
% 2.22/1.02      | v2_struct_0(X1)
% 2.22/1.02      | v2_struct_0(X3)
% 2.22/1.02      | v2_struct_0(X4)
% 2.22/1.02      | ~ v1_funct_1(X2)
% 2.22/1.02      | ~ l1_pre_topc(X1)
% 2.22/1.02      | ~ l1_pre_topc(X4)
% 2.22/1.02      | ~ v2_pre_topc(X1)
% 2.22/1.02      | ~ v2_pre_topc(X4) ),
% 2.22/1.02      inference(unflattening,[status(thm)],[c_533]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_2,plain,
% 2.22/1.02      ( ~ r2_hidden(X0,X1)
% 2.22/1.02      | m1_subset_1(X0,X2)
% 2.22/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.22/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_453,plain,
% 2.22/1.02      ( m1_subset_1(X0,X1)
% 2.22/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.22/1.02      | sK5 != X2
% 2.22/1.02      | sK6 != X0 ),
% 2.22/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_17]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_454,plain,
% 2.22/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0)) | m1_subset_1(sK6,X0) ),
% 2.22/1.02      inference(unflattening,[status(thm)],[c_453]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_559,plain,
% 2.22/1.02      ( r1_tmap_1(X0,X1,X2,sK6)
% 2.22/1.02      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
% 2.22/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.22/1.02      | ~ v3_pre_topc(sK5,X0)
% 2.22/1.02      | ~ m1_pre_topc(X3,X0)
% 2.22/1.02      | ~ m1_pre_topc(X3,X4)
% 2.22/1.02      | ~ m1_pre_topc(X0,X4)
% 2.22/1.02      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 2.22/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.22/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.22/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.22/1.02      | v2_struct_0(X0)
% 2.22/1.02      | v2_struct_0(X1)
% 2.22/1.02      | v2_struct_0(X3)
% 2.22/1.02      | v2_struct_0(X4)
% 2.22/1.02      | ~ v1_funct_1(X2)
% 2.22/1.02      | ~ l1_pre_topc(X1)
% 2.22/1.02      | ~ l1_pre_topc(X4)
% 2.22/1.02      | ~ v2_pre_topc(X1)
% 2.22/1.02      | ~ v2_pre_topc(X4) ),
% 2.22/1.02      inference(forward_subsumption_resolution,
% 2.22/1.02                [status(thm)],
% 2.22/1.02                [c_534,c_454]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_10,plain,
% 2.22/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.22/1.02      | ~ m1_pre_topc(X2,X0)
% 2.22/1.02      | m1_pre_topc(X2,X1)
% 2.22/1.02      | ~ l1_pre_topc(X1)
% 2.22/1.02      | ~ v2_pre_topc(X1) ),
% 2.22/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_580,plain,
% 2.22/1.02      ( r1_tmap_1(X0,X1,X2,sK6)
% 2.22/1.02      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
% 2.22/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.22/1.02      | ~ v3_pre_topc(sK5,X0)
% 2.22/1.02      | ~ m1_pre_topc(X3,X0)
% 2.22/1.02      | ~ m1_pre_topc(X0,X4)
% 2.22/1.02      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 2.22/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.22/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.22/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.22/1.02      | v2_struct_0(X0)
% 2.22/1.02      | v2_struct_0(X1)
% 2.22/1.02      | v2_struct_0(X3)
% 2.22/1.02      | v2_struct_0(X4)
% 2.22/1.02      | ~ v1_funct_1(X2)
% 2.22/1.02      | ~ l1_pre_topc(X1)
% 2.22/1.02      | ~ l1_pre_topc(X4)
% 2.22/1.02      | ~ v2_pre_topc(X1)
% 2.22/1.02      | ~ v2_pre_topc(X4) ),
% 2.22/1.02      inference(forward_subsumption_resolution,
% 2.22/1.02                [status(thm)],
% 2.22/1.02                [c_559,c_10]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_24,negated_conjecture,
% 2.22/1.02      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
% 2.22/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_606,plain,
% 2.22/1.02      ( r1_tmap_1(X0,X1,X2,sK6)
% 2.22/1.02      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
% 2.22/1.02      | ~ v3_pre_topc(sK5,X0)
% 2.22/1.02      | ~ m1_pre_topc(X3,X0)
% 2.22/1.02      | ~ m1_pre_topc(X0,X4)
% 2.22/1.02      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 2.22/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.22/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.22/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.22/1.02      | v2_struct_0(X0)
% 2.22/1.02      | v2_struct_0(X1)
% 2.22/1.02      | v2_struct_0(X3)
% 2.22/1.02      | v2_struct_0(X4)
% 2.22/1.02      | ~ v1_funct_1(X2)
% 2.22/1.02      | ~ l1_pre_topc(X1)
% 2.22/1.02      | ~ l1_pre_topc(X4)
% 2.22/1.02      | ~ v2_pre_topc(X1)
% 2.22/1.02      | ~ v2_pre_topc(X4)
% 2.22/1.02      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.22/1.02      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.22/1.02      | sK4 != X2 ),
% 2.22/1.02      inference(resolution_lifted,[status(thm)],[c_580,c_24]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_607,plain,
% 2.22/1.02      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 2.22/1.02      | r1_tmap_1(X3,X1,sK4,sK6)
% 2.22/1.02      | ~ v3_pre_topc(sK5,X3)
% 2.22/1.02      | ~ m1_pre_topc(X0,X3)
% 2.22/1.02      | ~ m1_pre_topc(X3,X2)
% 2.22/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.22/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.22/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.22/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.22/1.02      | v2_struct_0(X3)
% 2.22/1.02      | v2_struct_0(X1)
% 2.22/1.02      | v2_struct_0(X0)
% 2.22/1.02      | v2_struct_0(X2)
% 2.22/1.02      | ~ v1_funct_1(sK4)
% 2.22/1.02      | ~ l1_pre_topc(X1)
% 2.22/1.02      | ~ l1_pre_topc(X2)
% 2.22/1.02      | ~ v2_pre_topc(X1)
% 2.22/1.02      | ~ v2_pre_topc(X2)
% 2.22/1.02      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.22/1.02      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.22/1.02      inference(unflattening,[status(thm)],[c_606]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_25,negated_conjecture,
% 2.22/1.02      ( v1_funct_1(sK4) ),
% 2.22/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_611,plain,
% 2.22/1.02      ( v2_struct_0(X2)
% 2.22/1.02      | v2_struct_0(X0)
% 2.22/1.02      | v2_struct_0(X1)
% 2.22/1.02      | v2_struct_0(X3)
% 2.22/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.22/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.22/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.22/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.22/1.02      | ~ m1_pre_topc(X3,X2)
% 2.22/1.02      | ~ m1_pre_topc(X0,X3)
% 2.22/1.02      | ~ v3_pre_topc(sK5,X3)
% 2.22/1.02      | r1_tmap_1(X3,X1,sK4,sK6)
% 2.22/1.02      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 2.22/1.02      | ~ l1_pre_topc(X1)
% 2.22/1.02      | ~ l1_pre_topc(X2)
% 2.22/1.02      | ~ v2_pre_topc(X1)
% 2.22/1.02      | ~ v2_pre_topc(X2)
% 2.22/1.02      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.22/1.02      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.22/1.02      inference(global_propositional_subsumption,
% 2.22/1.02                [status(thm)],
% 2.22/1.02                [c_607,c_25]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_612,plain,
% 2.22/1.02      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 2.22/1.02      | r1_tmap_1(X3,X1,sK4,sK6)
% 2.22/1.02      | ~ v3_pre_topc(sK5,X3)
% 2.22/1.02      | ~ m1_pre_topc(X3,X2)
% 2.22/1.02      | ~ m1_pre_topc(X0,X3)
% 2.22/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.22/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.22/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.22/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.22/1.02      | v2_struct_0(X0)
% 2.22/1.02      | v2_struct_0(X1)
% 2.22/1.02      | v2_struct_0(X2)
% 2.22/1.02      | v2_struct_0(X3)
% 2.22/1.02      | ~ l1_pre_topc(X1)
% 2.22/1.02      | ~ l1_pre_topc(X2)
% 2.22/1.02      | ~ v2_pre_topc(X1)
% 2.22/1.02      | ~ v2_pre_topc(X2)
% 2.22/1.02      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.22/1.02      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.22/1.02      inference(renaming,[status(thm)],[c_611]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1731,plain,
% 2.22/1.02      ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),sK6)
% 2.22/1.02      | r1_tmap_1(X3_53,X1_53,sK4,sK6)
% 2.22/1.02      | ~ v3_pre_topc(sK5,X3_53)
% 2.22/1.02      | ~ m1_pre_topc(X3_53,X2_53)
% 2.22/1.02      | ~ m1_pre_topc(X0_53,X3_53)
% 2.22/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0_53))
% 2.22/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_53)))
% 2.22/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
% 2.22/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
% 2.22/1.02      | v2_struct_0(X1_53)
% 2.22/1.02      | v2_struct_0(X2_53)
% 2.22/1.02      | v2_struct_0(X3_53)
% 2.22/1.02      | v2_struct_0(X0_53)
% 2.22/1.02      | ~ l1_pre_topc(X1_53)
% 2.22/1.02      | ~ l1_pre_topc(X2_53)
% 2.22/1.02      | ~ v2_pre_topc(X1_53)
% 2.22/1.02      | ~ v2_pre_topc(X2_53)
% 2.22/1.02      | u1_struct_0(X3_53) != u1_struct_0(sK3)
% 2.22/1.02      | u1_struct_0(X1_53) != u1_struct_0(sK0) ),
% 2.22/1.02      inference(subtyping,[status(esa)],[c_612]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_3670,plain,
% 2.22/1.02      ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,sK3,X0_53,sK4),sK6)
% 2.22/1.02      | r1_tmap_1(sK3,X1_53,sK4,sK6)
% 2.22/1.02      | ~ v3_pre_topc(sK5,sK3)
% 2.22/1.02      | ~ m1_pre_topc(X0_53,sK3)
% 2.22/1.02      | ~ m1_pre_topc(sK3,X2_53)
% 2.22/1.02      | ~ r1_tarski(sK5,u1_struct_0(X0_53))
% 2.22/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.22/1.02      | ~ m1_subset_1(sK6,u1_struct_0(X0_53))
% 2.22/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
% 2.22/1.02      | v2_struct_0(X1_53)
% 2.22/1.02      | v2_struct_0(X2_53)
% 2.22/1.02      | v2_struct_0(X0_53)
% 2.22/1.02      | v2_struct_0(sK3)
% 2.22/1.02      | ~ l1_pre_topc(X1_53)
% 2.22/1.02      | ~ l1_pre_topc(X2_53)
% 2.22/1.02      | ~ v2_pre_topc(X1_53)
% 2.22/1.02      | ~ v2_pre_topc(X2_53)
% 2.22/1.02      | u1_struct_0(X1_53) != u1_struct_0(sK0)
% 2.22/1.02      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.22/1.02      inference(instantiation,[status(thm)],[c_1731]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_3899,plain,
% 2.22/1.02      ( r1_tmap_1(sK3,X0_53,sK4,sK6)
% 2.22/1.02      | ~ r1_tmap_1(sK2,X0_53,k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4),sK6)
% 2.22/1.02      | ~ v3_pre_topc(sK5,sK3)
% 2.22/1.02      | ~ m1_pre_topc(sK3,X1_53)
% 2.22/1.02      | ~ m1_pre_topc(sK2,sK3)
% 2.22/1.02      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 2.22/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.22/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 2.22/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 2.22/1.02      | v2_struct_0(X1_53)
% 2.22/1.02      | v2_struct_0(X0_53)
% 2.22/1.02      | v2_struct_0(sK3)
% 2.22/1.02      | v2_struct_0(sK2)
% 2.22/1.02      | ~ l1_pre_topc(X1_53)
% 2.22/1.02      | ~ l1_pre_topc(X0_53)
% 2.22/1.02      | ~ v2_pre_topc(X1_53)
% 2.22/1.02      | ~ v2_pre_topc(X0_53)
% 2.22/1.02      | u1_struct_0(X0_53) != u1_struct_0(sK0)
% 2.22/1.02      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.22/1.02      inference(instantiation,[status(thm)],[c_3670]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_4204,plain,
% 2.22/1.03      ( r1_tmap_1(sK3,X0_53,sK4,sK6)
% 2.22/1.03      | ~ r1_tmap_1(sK2,X0_53,k3_tmap_1(sK1,X0_53,sK3,sK2,sK4),sK6)
% 2.22/1.03      | ~ v3_pre_topc(sK5,sK3)
% 2.22/1.03      | ~ m1_pre_topc(sK3,sK1)
% 2.22/1.03      | ~ m1_pre_topc(sK2,sK3)
% 2.22/1.03      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 2.22/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.22/1.03      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 2.22/1.03      | v2_struct_0(X0_53)
% 2.22/1.03      | v2_struct_0(sK3)
% 2.22/1.03      | v2_struct_0(sK1)
% 2.22/1.03      | v2_struct_0(sK2)
% 2.22/1.03      | ~ l1_pre_topc(X0_53)
% 2.22/1.03      | ~ l1_pre_topc(sK1)
% 2.22/1.03      | ~ v2_pre_topc(X0_53)
% 2.22/1.03      | ~ v2_pre_topc(sK1)
% 2.22/1.03      | u1_struct_0(X0_53) != u1_struct_0(sK0)
% 2.22/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_3899]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_4206,plain,
% 2.22/1.03      ( r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.22/1.03      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 2.22/1.03      | ~ v3_pre_topc(sK5,sK3)
% 2.22/1.03      | ~ m1_pre_topc(sK3,sK1)
% 2.22/1.03      | ~ m1_pre_topc(sK2,sK3)
% 2.22/1.03      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 2.22/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.22/1.03      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
% 2.22/1.03      | v2_struct_0(sK3)
% 2.22/1.03      | v2_struct_0(sK1)
% 2.22/1.03      | v2_struct_0(sK0)
% 2.22/1.03      | v2_struct_0(sK2)
% 2.22/1.03      | ~ l1_pre_topc(sK1)
% 2.22/1.03      | ~ l1_pre_topc(sK0)
% 2.22/1.03      | ~ v2_pre_topc(sK1)
% 2.22/1.03      | ~ v2_pre_topc(sK0)
% 2.22/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_4204]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3021,plain,
% 2.22/1.03      ( r1_tmap_1(sK2,sK0,X0_54,X1_54)
% 2.22/1.03      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 2.22/1.03      | X0_54 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 2.22/1.03      | X1_54 != sK7 ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1773]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3197,plain,
% 2.22/1.03      ( r1_tmap_1(sK2,sK0,X0_54,sK6)
% 2.22/1.03      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 2.22/1.03      | X0_54 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 2.22/1.03      | sK6 != sK7 ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_3021]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3975,plain,
% 2.22/1.03      ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 2.22/1.03      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 2.22/1.03      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 2.22/1.03      | sK6 != sK7 ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_3197]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_9,plain,
% 2.22/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.22/1.03      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.22/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.22/1.03      | ~ m1_pre_topc(X4,X0)
% 2.22/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.22/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.22/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.22/1.03      | v2_struct_0(X1)
% 2.22/1.03      | v2_struct_0(X0)
% 2.22/1.03      | v2_struct_0(X4)
% 2.22/1.03      | ~ v1_funct_1(X2)
% 2.22/1.03      | ~ l1_pre_topc(X1)
% 2.22/1.03      | ~ l1_pre_topc(X0)
% 2.22/1.03      | ~ v2_pre_topc(X1)
% 2.22/1.03      | ~ v2_pre_topc(X0) ),
% 2.22/1.03      inference(cnf_transformation,[],[f84]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_744,plain,
% 2.22/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.22/1.03      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.22/1.03      | ~ m1_pre_topc(X4,X0)
% 2.22/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.22/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.22/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.22/1.03      | v2_struct_0(X0)
% 2.22/1.03      | v2_struct_0(X1)
% 2.22/1.03      | v2_struct_0(X4)
% 2.22/1.03      | ~ v1_funct_1(X2)
% 2.22/1.03      | ~ l1_pre_topc(X0)
% 2.22/1.03      | ~ l1_pre_topc(X1)
% 2.22/1.03      | ~ v2_pre_topc(X0)
% 2.22/1.03      | ~ v2_pre_topc(X1)
% 2.22/1.03      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.22/1.03      | sK4 != X2 ),
% 2.22/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_745,plain,
% 2.22/1.03      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.22/1.03      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.22/1.03      | ~ m1_pre_topc(X0,X2)
% 2.22/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.22/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.22/1.03      | v2_struct_0(X2)
% 2.22/1.03      | v2_struct_0(X1)
% 2.22/1.03      | v2_struct_0(X0)
% 2.22/1.03      | ~ v1_funct_1(sK4)
% 2.22/1.03      | ~ l1_pre_topc(X2)
% 2.22/1.03      | ~ l1_pre_topc(X1)
% 2.22/1.03      | ~ v2_pre_topc(X2)
% 2.22/1.03      | ~ v2_pre_topc(X1)
% 2.22/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.22/1.03      inference(unflattening,[status(thm)],[c_744]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_749,plain,
% 2.22/1.03      ( v2_struct_0(X0)
% 2.22/1.03      | v2_struct_0(X1)
% 2.22/1.03      | v2_struct_0(X2)
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.22/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.22/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.22/1.03      | ~ m1_pre_topc(X0,X2)
% 2.22/1.03      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.22/1.03      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.22/1.03      | ~ l1_pre_topc(X2)
% 2.22/1.03      | ~ l1_pre_topc(X1)
% 2.22/1.03      | ~ v2_pre_topc(X2)
% 2.22/1.03      | ~ v2_pre_topc(X1)
% 2.22/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.22/1.03      inference(global_propositional_subsumption,
% 2.22/1.03                [status(thm)],
% 2.22/1.03                [c_745,c_25]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_750,plain,
% 2.22/1.03      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.22/1.03      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.22/1.03      | ~ m1_pre_topc(X0,X2)
% 2.22/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.22/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.22/1.03      | v2_struct_0(X0)
% 2.22/1.03      | v2_struct_0(X1)
% 2.22/1.03      | v2_struct_0(X2)
% 2.22/1.03      | ~ l1_pre_topc(X1)
% 2.22/1.03      | ~ l1_pre_topc(X2)
% 2.22/1.03      | ~ v2_pre_topc(X1)
% 2.22/1.03      | ~ v2_pre_topc(X2)
% 2.22/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.22/1.03      inference(renaming,[status(thm)],[c_749]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1729,plain,
% 2.22/1.03      ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,sK4,X0_53),X0_54)
% 2.22/1.03      | ~ r1_tmap_1(X2_53,X1_53,sK4,X0_54)
% 2.22/1.03      | ~ m1_pre_topc(X0_53,X2_53)
% 2.22/1.03      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 2.22/1.03      | ~ m1_subset_1(X0_54,u1_struct_0(X2_53))
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 2.22/1.03      | v2_struct_0(X1_53)
% 2.22/1.03      | v2_struct_0(X2_53)
% 2.22/1.03      | v2_struct_0(X0_53)
% 2.22/1.03      | ~ l1_pre_topc(X1_53)
% 2.22/1.03      | ~ l1_pre_topc(X2_53)
% 2.22/1.03      | ~ v2_pre_topc(X1_53)
% 2.22/1.03      | ~ v2_pre_topc(X2_53)
% 2.22/1.03      | u1_struct_0(X2_53) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(X1_53) != u1_struct_0(sK0) ),
% 2.22/1.03      inference(subtyping,[status(esa)],[c_750]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3213,plain,
% 2.22/1.03      ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK3,X1_53,sK4,X0_53),X0_54)
% 2.22/1.03      | ~ r1_tmap_1(sK3,X1_53,sK4,X0_54)
% 2.22/1.03      | ~ m1_pre_topc(X0_53,sK3)
% 2.22/1.03      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 2.22/1.03      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
% 2.22/1.03      | v2_struct_0(X1_53)
% 2.22/1.03      | v2_struct_0(X0_53)
% 2.22/1.03      | v2_struct_0(sK3)
% 2.22/1.03      | ~ l1_pre_topc(X1_53)
% 2.22/1.03      | ~ l1_pre_topc(sK3)
% 2.22/1.03      | ~ v2_pre_topc(X1_53)
% 2.22/1.03      | ~ v2_pre_topc(sK3)
% 2.22/1.03      | u1_struct_0(X1_53) != u1_struct_0(sK0)
% 2.22/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1729]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3736,plain,
% 2.22/1.03      ( ~ r1_tmap_1(sK3,X0_53,sK4,X0_54)
% 2.22/1.03      | r1_tmap_1(sK2,X0_53,k2_tmap_1(sK3,X0_53,sK4,sK2),X0_54)
% 2.22/1.03      | ~ m1_pre_topc(sK2,sK3)
% 2.22/1.03      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.22/1.03      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 2.22/1.03      | v2_struct_0(X0_53)
% 2.22/1.03      | v2_struct_0(sK3)
% 2.22/1.03      | v2_struct_0(sK2)
% 2.22/1.03      | ~ l1_pre_topc(X0_53)
% 2.22/1.03      | ~ l1_pre_topc(sK3)
% 2.22/1.03      | ~ v2_pre_topc(X0_53)
% 2.22/1.03      | ~ v2_pre_topc(sK3)
% 2.22/1.03      | u1_struct_0(X0_53) != u1_struct_0(sK0)
% 2.22/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_3213]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3888,plain,
% 2.22/1.03      ( ~ r1_tmap_1(sK3,X0_53,sK4,sK6)
% 2.22/1.03      | r1_tmap_1(sK2,X0_53,k2_tmap_1(sK3,X0_53,sK4,sK2),sK6)
% 2.22/1.03      | ~ m1_pre_topc(sK2,sK3)
% 2.22/1.03      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.22/1.03      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 2.22/1.03      | v2_struct_0(X0_53)
% 2.22/1.03      | v2_struct_0(sK3)
% 2.22/1.03      | v2_struct_0(sK2)
% 2.22/1.03      | ~ l1_pre_topc(X0_53)
% 2.22/1.03      | ~ l1_pre_topc(sK3)
% 2.22/1.03      | ~ v2_pre_topc(X0_53)
% 2.22/1.03      | ~ v2_pre_topc(sK3)
% 2.22/1.03      | u1_struct_0(X0_53) != u1_struct_0(sK0)
% 2.22/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_3736]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3890,plain,
% 2.22/1.03      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.22/1.03      | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
% 2.22/1.03      | ~ m1_pre_topc(sK2,sK3)
% 2.22/1.03      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.22/1.03      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
% 2.22/1.03      | v2_struct_0(sK3)
% 2.22/1.03      | v2_struct_0(sK0)
% 2.22/1.03      | v2_struct_0(sK2)
% 2.22/1.03      | ~ l1_pre_topc(sK3)
% 2.22/1.03      | ~ l1_pre_topc(sK0)
% 2.22/1.03      | ~ v2_pre_topc(sK3)
% 2.22/1.03      | ~ v2_pre_topc(sK0)
% 2.22/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_3888]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1762,plain,( X0_55 = X0_55 ),theory(equality) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3828,plain,
% 2.22/1.03      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1762]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_7,plain,
% 2.22/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.22/1.03      | ~ m1_pre_topc(X3,X1)
% 2.22/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.22/1.03      | v2_struct_0(X1)
% 2.22/1.03      | v2_struct_0(X2)
% 2.22/1.03      | ~ v1_funct_1(X0)
% 2.22/1.03      | ~ l1_pre_topc(X1)
% 2.22/1.03      | ~ l1_pre_topc(X2)
% 2.22/1.03      | ~ v2_pre_topc(X1)
% 2.22/1.03      | ~ v2_pre_topc(X2)
% 2.22/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.22/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_849,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0,X1)
% 2.22/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.22/1.03      | v2_struct_0(X1)
% 2.22/1.03      | v2_struct_0(X3)
% 2.22/1.03      | ~ v1_funct_1(X2)
% 2.22/1.03      | ~ l1_pre_topc(X1)
% 2.22/1.03      | ~ l1_pre_topc(X3)
% 2.22/1.03      | ~ v2_pre_topc(X1)
% 2.22/1.03      | ~ v2_pre_topc(X3)
% 2.22/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 2.22/1.03      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(X3) != u1_struct_0(sK0)
% 2.22/1.03      | sK4 != X2 ),
% 2.22/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_24]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_850,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0,X1)
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.22/1.03      | v2_struct_0(X1)
% 2.22/1.03      | v2_struct_0(X2)
% 2.22/1.03      | ~ v1_funct_1(sK4)
% 2.22/1.03      | ~ l1_pre_topc(X1)
% 2.22/1.03      | ~ l1_pre_topc(X2)
% 2.22/1.03      | ~ v2_pre_topc(X1)
% 2.22/1.03      | ~ v2_pre_topc(X2)
% 2.22/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 2.22/1.03      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(X2) != u1_struct_0(sK0) ),
% 2.22/1.03      inference(unflattening,[status(thm)],[c_849]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_854,plain,
% 2.22/1.03      ( v2_struct_0(X2)
% 2.22/1.03      | v2_struct_0(X1)
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.22/1.03      | ~ m1_pre_topc(X0,X1)
% 2.22/1.03      | ~ l1_pre_topc(X1)
% 2.22/1.03      | ~ l1_pre_topc(X2)
% 2.22/1.03      | ~ v2_pre_topc(X1)
% 2.22/1.03      | ~ v2_pre_topc(X2)
% 2.22/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 2.22/1.03      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(X2) != u1_struct_0(sK0) ),
% 2.22/1.03      inference(global_propositional_subsumption,
% 2.22/1.03                [status(thm)],
% 2.22/1.03                [c_850,c_25]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_855,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0,X1)
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.22/1.03      | v2_struct_0(X1)
% 2.22/1.03      | v2_struct_0(X2)
% 2.22/1.03      | ~ l1_pre_topc(X1)
% 2.22/1.03      | ~ l1_pre_topc(X2)
% 2.22/1.03      | ~ v2_pre_topc(X1)
% 2.22/1.03      | ~ v2_pre_topc(X2)
% 2.22/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 2.22/1.03      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(X2) != u1_struct_0(sK0) ),
% 2.22/1.03      inference(renaming,[status(thm)],[c_854]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1727,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X2_53))))
% 2.22/1.03      | v2_struct_0(X1_53)
% 2.22/1.03      | v2_struct_0(X2_53)
% 2.22/1.03      | ~ l1_pre_topc(X1_53)
% 2.22/1.03      | ~ l1_pre_topc(X2_53)
% 2.22/1.03      | ~ v2_pre_topc(X1_53)
% 2.22/1.03      | ~ v2_pre_topc(X2_53)
% 2.22/1.03      | u1_struct_0(X1_53) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(X2_53) != u1_struct_0(sK0)
% 2.22/1.03      | k2_partfun1(u1_struct_0(X1_53),u1_struct_0(X2_53),sK4,u1_struct_0(X0_53)) = k2_tmap_1(X1_53,X2_53,sK4,X0_53) ),
% 2.22/1.03      inference(subtyping,[status(esa)],[c_855]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2923,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0_53,sK3)
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
% 2.22/1.03      | v2_struct_0(X1_53)
% 2.22/1.03      | v2_struct_0(sK3)
% 2.22/1.03      | ~ l1_pre_topc(X1_53)
% 2.22/1.03      | ~ l1_pre_topc(sK3)
% 2.22/1.03      | ~ v2_pre_topc(X1_53)
% 2.22/1.03      | ~ v2_pre_topc(sK3)
% 2.22/1.03      | u1_struct_0(X1_53) != u1_struct_0(sK0)
% 2.22/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.22/1.03      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1_53),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK3,X1_53,sK4,X0_53) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1727]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3731,plain,
% 2.22/1.03      ( ~ m1_pre_topc(sK2,sK3)
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 2.22/1.03      | v2_struct_0(X0_53)
% 2.22/1.03      | v2_struct_0(sK3)
% 2.22/1.03      | ~ l1_pre_topc(X0_53)
% 2.22/1.03      | ~ l1_pre_topc(sK3)
% 2.22/1.03      | ~ v2_pre_topc(X0_53)
% 2.22/1.03      | ~ v2_pre_topc(sK3)
% 2.22/1.03      | u1_struct_0(X0_53) != u1_struct_0(sK0)
% 2.22/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.22/1.03      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0_53),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,X0_53,sK4,sK2) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_2923]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3733,plain,
% 2.22/1.03      ( ~ m1_pre_topc(sK2,sK3)
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
% 2.22/1.03      | v2_struct_0(sK3)
% 2.22/1.03      | v2_struct_0(sK0)
% 2.22/1.03      | ~ l1_pre_topc(sK3)
% 2.22/1.03      | ~ l1_pre_topc(sK0)
% 2.22/1.03      | ~ v2_pre_topc(sK3)
% 2.22/1.03      | ~ v2_pre_topc(sK0)
% 2.22/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 2.22/1.03      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK0,sK4,sK2) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_3731]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_8,plain,
% 2.22/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.22/1.03      | ~ m1_pre_topc(X1,X3)
% 2.22/1.03      | ~ m1_pre_topc(X4,X3)
% 2.22/1.03      | ~ m1_pre_topc(X4,X1)
% 2.22/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.22/1.03      | v2_struct_0(X3)
% 2.22/1.03      | v2_struct_0(X2)
% 2.22/1.03      | ~ v1_funct_1(X0)
% 2.22/1.03      | ~ l1_pre_topc(X3)
% 2.22/1.03      | ~ l1_pre_topc(X2)
% 2.22/1.03      | ~ v2_pre_topc(X3)
% 2.22/1.03      | ~ v2_pre_topc(X2)
% 2.22/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X4)) = k3_tmap_1(X3,X2,X1,X4,X0) ),
% 2.22/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_801,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0,X1)
% 2.22/1.03      | ~ m1_pre_topc(X2,X1)
% 2.22/1.03      | ~ m1_pre_topc(X2,X0)
% 2.22/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X4))))
% 2.22/1.03      | v2_struct_0(X4)
% 2.22/1.03      | v2_struct_0(X1)
% 2.22/1.03      | ~ v1_funct_1(X3)
% 2.22/1.03      | ~ l1_pre_topc(X4)
% 2.22/1.03      | ~ l1_pre_topc(X1)
% 2.22/1.03      | ~ v2_pre_topc(X4)
% 2.22/1.03      | ~ v2_pre_topc(X1)
% 2.22/1.03      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X4),X3,u1_struct_0(X2)) = k3_tmap_1(X1,X4,X0,X2,X3)
% 2.22/1.03      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(X4) != u1_struct_0(sK0)
% 2.22/1.03      | sK4 != X3 ),
% 2.22/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_802,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0,X1)
% 2.22/1.03      | ~ m1_pre_topc(X2,X0)
% 2.22/1.03      | ~ m1_pre_topc(X2,X1)
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
% 2.22/1.03      | v2_struct_0(X1)
% 2.22/1.03      | v2_struct_0(X3)
% 2.22/1.03      | ~ v1_funct_1(sK4)
% 2.22/1.03      | ~ l1_pre_topc(X1)
% 2.22/1.03      | ~ l1_pre_topc(X3)
% 2.22/1.03      | ~ v2_pre_topc(X1)
% 2.22/1.03      | ~ v2_pre_topc(X3)
% 2.22/1.03      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK4,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK4)
% 2.22/1.03      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(X3) != u1_struct_0(sK0) ),
% 2.22/1.03      inference(unflattening,[status(thm)],[c_801]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_806,plain,
% 2.22/1.03      ( v2_struct_0(X3)
% 2.22/1.03      | v2_struct_0(X1)
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
% 2.22/1.03      | ~ m1_pre_topc(X0,X1)
% 2.22/1.03      | ~ m1_pre_topc(X2,X0)
% 2.22/1.03      | ~ l1_pre_topc(X1)
% 2.22/1.03      | ~ l1_pre_topc(X3)
% 2.22/1.03      | ~ v2_pre_topc(X1)
% 2.22/1.03      | ~ v2_pre_topc(X3)
% 2.22/1.03      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK4,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK4)
% 2.22/1.03      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(X3) != u1_struct_0(sK0) ),
% 2.22/1.03      inference(global_propositional_subsumption,
% 2.22/1.03                [status(thm)],
% 2.22/1.03                [c_802,c_25,c_10]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_807,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0,X1)
% 2.22/1.03      | ~ m1_pre_topc(X2,X0)
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
% 2.22/1.03      | v2_struct_0(X1)
% 2.22/1.03      | v2_struct_0(X3)
% 2.22/1.03      | ~ l1_pre_topc(X1)
% 2.22/1.03      | ~ l1_pre_topc(X3)
% 2.22/1.03      | ~ v2_pre_topc(X1)
% 2.22/1.03      | ~ v2_pre_topc(X3)
% 2.22/1.03      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK4,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK4)
% 2.22/1.03      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(X3) != u1_struct_0(sK0) ),
% 2.22/1.03      inference(renaming,[status(thm)],[c_806]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1728,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.22/1.03      | ~ m1_pre_topc(X2_53,X0_53)
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X3_53))))
% 2.22/1.03      | v2_struct_0(X1_53)
% 2.22/1.03      | v2_struct_0(X3_53)
% 2.22/1.03      | ~ l1_pre_topc(X1_53)
% 2.22/1.03      | ~ l1_pre_topc(X3_53)
% 2.22/1.03      | ~ v2_pre_topc(X1_53)
% 2.22/1.03      | ~ v2_pre_topc(X3_53)
% 2.22/1.03      | u1_struct_0(X0_53) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(X3_53) != u1_struct_0(sK0)
% 2.22/1.03      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X3_53),sK4,u1_struct_0(X2_53)) = k3_tmap_1(X1_53,X3_53,X0_53,X2_53,sK4) ),
% 2.22/1.03      inference(subtyping,[status(esa)],[c_807]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3208,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0_53,sK3)
% 2.22/1.03      | ~ m1_pre_topc(sK3,X1_53)
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2_53))))
% 2.22/1.03      | v2_struct_0(X2_53)
% 2.22/1.03      | v2_struct_0(X1_53)
% 2.22/1.03      | ~ l1_pre_topc(X2_53)
% 2.22/1.03      | ~ l1_pre_topc(X1_53)
% 2.22/1.03      | ~ v2_pre_topc(X2_53)
% 2.22/1.03      | ~ v2_pre_topc(X1_53)
% 2.22/1.03      | u1_struct_0(X2_53) != u1_struct_0(sK0)
% 2.22/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.22/1.03      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X2_53),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,X2_53,sK3,X0_53,sK4) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1728]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3445,plain,
% 2.22/1.03      ( ~ m1_pre_topc(sK3,X0_53)
% 2.22/1.03      | ~ m1_pre_topc(sK2,sK3)
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
% 2.22/1.03      | v2_struct_0(X1_53)
% 2.22/1.03      | v2_struct_0(X0_53)
% 2.22/1.03      | ~ l1_pre_topc(X1_53)
% 2.22/1.03      | ~ l1_pre_topc(X0_53)
% 2.22/1.03      | ~ v2_pre_topc(X1_53)
% 2.22/1.03      | ~ v2_pre_topc(X0_53)
% 2.22/1.03      | u1_struct_0(X1_53) != u1_struct_0(sK0)
% 2.22/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.22/1.03      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1_53),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0_53,X1_53,sK3,sK2,sK4) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_3208]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3652,plain,
% 2.22/1.03      ( ~ m1_pre_topc(sK3,sK1)
% 2.22/1.03      | ~ m1_pre_topc(sK2,sK3)
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 2.22/1.03      | v2_struct_0(X0_53)
% 2.22/1.03      | v2_struct_0(sK1)
% 2.22/1.03      | ~ l1_pre_topc(X0_53)
% 2.22/1.03      | ~ l1_pre_topc(sK1)
% 2.22/1.03      | ~ v2_pre_topc(X0_53)
% 2.22/1.03      | ~ v2_pre_topc(sK1)
% 2.22/1.03      | u1_struct_0(X0_53) != u1_struct_0(sK0)
% 2.22/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.22/1.03      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0_53),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK1,X0_53,sK3,sK2,sK4) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_3445]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3654,plain,
% 2.22/1.03      ( ~ m1_pre_topc(sK3,sK1)
% 2.22/1.03      | ~ m1_pre_topc(sK2,sK3)
% 2.22/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
% 2.22/1.03      | v2_struct_0(sK1)
% 2.22/1.03      | v2_struct_0(sK0)
% 2.22/1.03      | ~ l1_pre_topc(sK1)
% 2.22/1.03      | ~ l1_pre_topc(sK0)
% 2.22/1.03      | ~ v2_pre_topc(sK1)
% 2.22/1.03      | ~ v2_pre_topc(sK0)
% 2.22/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.22/1.03      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 2.22/1.03      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_3652]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_26,negated_conjecture,
% 2.22/1.03      ( m1_pre_topc(sK3,sK1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1742,negated_conjecture,
% 2.22/1.03      ( m1_pre_topc(sK3,sK1) ),
% 2.22/1.03      inference(subtyping,[status(esa)],[c_26]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2559,plain,
% 2.22/1.03      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_1742]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0,X1)
% 2.22/1.03      | ~ l1_pre_topc(X1)
% 2.22/1.03      | ~ v2_pre_topc(X1)
% 2.22/1.03      | v2_pre_topc(X0) ),
% 2.22/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1757,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.22/1.03      | ~ l1_pre_topc(X1_53)
% 2.22/1.03      | ~ v2_pre_topc(X1_53)
% 2.22/1.03      | v2_pre_topc(X0_53) ),
% 2.22/1.03      inference(subtyping,[status(esa)],[c_3]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2545,plain,
% 2.22/1.03      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.22/1.03      | l1_pre_topc(X1_53) != iProver_top
% 2.22/1.03      | v2_pre_topc(X1_53) != iProver_top
% 2.22/1.03      | v2_pre_topc(X0_53) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_1757]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3521,plain,
% 2.22/1.03      ( l1_pre_topc(sK1) != iProver_top
% 2.22/1.03      | v2_pre_topc(sK3) = iProver_top
% 2.22/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_2559,c_2545]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3542,plain,
% 2.22/1.03      ( ~ l1_pre_topc(sK1) | v2_pre_topc(sK3) | ~ v2_pre_topc(sK1) ),
% 2.22/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_3521]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1772,plain,
% 2.22/1.03      ( X0_54 != X1_54
% 2.22/1.03      | k3_tmap_1(X0_53,X1_53,X2_53,X3_53,X0_54) = k3_tmap_1(X0_53,X1_53,X2_53,X3_53,X1_54) ),
% 2.22/1.03      theory(equality) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3427,plain,
% 2.22/1.03      ( X0_54 != sK4
% 2.22/1.03      | k3_tmap_1(sK1,sK0,sK3,sK2,X0_54) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1772]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3430,plain,
% 2.22/1.03      ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 2.22/1.03      | sK4 != sK4 ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_3427]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_4,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.22/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1756,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.22/1.03      | ~ l1_pre_topc(X1_53)
% 2.22/1.03      | l1_pre_topc(X0_53) ),
% 2.22/1.03      inference(subtyping,[status(esa)],[c_4]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3247,plain,
% 2.22/1.03      ( ~ m1_pre_topc(sK3,X0_53)
% 2.22/1.03      | ~ l1_pre_topc(X0_53)
% 2.22/1.03      | l1_pre_topc(sK3) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1756]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3375,plain,
% 2.22/1.03      ( ~ m1_pre_topc(sK3,sK1) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK1) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_3247]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3144,plain,
% 2.22/1.03      ( X0_54 != X1_54 | X0_54 = sK6 | sK6 != X1_54 ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1763]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3320,plain,
% 2.22/1.03      ( X0_54 = sK6 | X0_54 != sK7 | sK6 != sK7 ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_3144]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3354,plain,
% 2.22/1.03      ( sK6 != sK7 | sK7 = sK6 | sK7 != sK7 ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_3320]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1761,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3139,plain,
% 2.22/1.03      ( sK6 = sK6 ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1761]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3127,plain,
% 2.22/1.03      ( sK7 = sK7 ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1761]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_5,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0,X1)
% 2.22/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.22/1.03      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/1.03      | ~ l1_pre_topc(X1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1755,plain,
% 2.22/1.03      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.22/1.03      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.22/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X1_53)))
% 2.22/1.03      | ~ l1_pre_topc(X1_53) ),
% 2.22/1.03      inference(subtyping,[status(esa)],[c_5]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2957,plain,
% 2.22/1.03      ( ~ m1_pre_topc(sK2,sK3)
% 2.22/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.22/1.03      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/1.03      | ~ l1_pre_topc(sK3) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1755]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3115,plain,
% 2.22/1.03      ( ~ m1_pre_topc(sK2,sK3)
% 2.22/1.03      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.22/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/1.03      | ~ l1_pre_topc(sK3) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_2957]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_6,plain,
% 2.22/1.03      ( ~ v3_pre_topc(X0,X1)
% 2.22/1.03      | v3_pre_topc(X0,X2)
% 2.22/1.03      | ~ m1_pre_topc(X2,X1)
% 2.22/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.22/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/1.03      | ~ l1_pre_topc(X1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f83]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1754,plain,
% 2.22/1.03      ( ~ v3_pre_topc(X0_54,X0_53)
% 2.22/1.03      | v3_pre_topc(X0_54,X1_53)
% 2.22/1.03      | ~ m1_pre_topc(X1_53,X0_53)
% 2.22/1.03      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X1_53)))
% 2.22/1.03      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.22/1.03      | ~ l1_pre_topc(X0_53) ),
% 2.22/1.03      inference(subtyping,[status(esa)],[c_6]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3016,plain,
% 2.22/1.03      ( v3_pre_topc(sK5,X0_53)
% 2.22/1.03      | ~ v3_pre_topc(sK5,sK1)
% 2.22/1.03      | ~ m1_pre_topc(X0_53,sK1)
% 2.22/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.22/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/1.03      | ~ l1_pre_topc(sK1) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1754]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3114,plain,
% 2.22/1.03      ( v3_pre_topc(sK5,sK3)
% 2.22/1.03      | ~ v3_pre_topc(sK5,sK1)
% 2.22/1.03      | ~ m1_pre_topc(sK3,sK1)
% 2.22/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.22/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/1.03      | ~ l1_pre_topc(sK1) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_3016]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1732,plain,
% 2.22/1.03      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0_55)) | m1_subset_1(sK6,X0_55) ),
% 2.22/1.03      inference(subtyping,[status(esa)],[c_454]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3048,plain,
% 2.22/1.03      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/1.03      | m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1732]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2922,plain,
% 2.22/1.03      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1762]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_15,negated_conjecture,
% 2.22/1.03      ( sK6 = sK7 ),
% 2.22/1.03      inference(cnf_transformation,[],[f80]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1750,negated_conjecture,
% 2.22/1.03      ( sK6 = sK7 ),
% 2.22/1.03      inference(subtyping,[status(esa)],[c_15]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1784,plain,
% 2.22/1.03      ( sK4 = sK4 ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1761]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_0,plain,
% 2.22/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.22/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_233,plain,
% 2.22/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.22/1.03      inference(prop_impl,[status(thm)],[c_0]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_16,negated_conjecture,
% 2.22/1.03      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 2.22/1.03      inference(cnf_transformation,[],[f79]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_900,plain,
% 2.22/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.22/1.03      | u1_struct_0(sK2) != X1
% 2.22/1.03      | sK5 != X0 ),
% 2.22/1.03      inference(resolution_lifted,[status(thm)],[c_233,c_16]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_901,plain,
% 2.22/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.22/1.03      inference(unflattening,[status(thm)],[c_900]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_13,negated_conjecture,
% 2.22/1.03      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.22/1.03      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 2.22/1.03      inference(cnf_transformation,[],[f82]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_14,negated_conjecture,
% 2.22/1.03      ( r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.22/1.03      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 2.22/1.03      inference(cnf_transformation,[],[f81]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_18,negated_conjecture,
% 2.22/1.03      ( v3_pre_topc(sK5,sK1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f77]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_20,negated_conjecture,
% 2.22/1.03      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.22/1.03      inference(cnf_transformation,[],[f75]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_21,negated_conjecture,
% 2.22/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.22/1.03      inference(cnf_transformation,[],[f74]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_22,negated_conjecture,
% 2.22/1.03      ( m1_pre_topc(sK2,sK3) ),
% 2.22/1.03      inference(cnf_transformation,[],[f73]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_23,negated_conjecture,
% 2.22/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
% 2.22/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_27,negated_conjecture,
% 2.22/1.03      ( ~ v2_struct_0(sK3) ),
% 2.22/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_29,negated_conjecture,
% 2.22/1.03      ( ~ v2_struct_0(sK2) ),
% 2.22/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_30,negated_conjecture,
% 2.22/1.03      ( l1_pre_topc(sK1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f65]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_31,negated_conjecture,
% 2.22/1.03      ( v2_pre_topc(sK1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_32,negated_conjecture,
% 2.22/1.03      ( ~ v2_struct_0(sK1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f63]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_33,negated_conjecture,
% 2.22/1.03      ( l1_pre_topc(sK0) ),
% 2.22/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_34,negated_conjecture,
% 2.22/1.03      ( v2_pre_topc(sK0) ),
% 2.22/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_35,negated_conjecture,
% 2.22/1.03      ( ~ v2_struct_0(sK0) ),
% 2.22/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(contradiction,plain,
% 2.22/1.03      ( $false ),
% 2.22/1.03      inference(minisat,
% 2.22/1.03                [status(thm)],
% 2.22/1.03                [c_5062,c_5029,c_4527,c_4206,c_3975,c_3890,c_3828,c_3733,
% 2.22/1.03                 c_3654,c_3542,c_3430,c_3375,c_3354,c_3139,c_3127,c_3115,
% 2.22/1.03                 c_3114,c_3048,c_2922,c_1750,c_1784,c_901,c_13,c_14,c_16,
% 2.22/1.03                 c_18,c_20,c_21,c_22,c_23,c_26,c_27,c_29,c_30,c_31,c_32,
% 2.22/1.03                 c_33,c_34,c_35]) ).
% 2.22/1.03  
% 2.22/1.03  
% 2.22/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.22/1.03  
% 2.22/1.03  ------                               Statistics
% 2.22/1.03  
% 2.22/1.03  ------ General
% 2.22/1.03  
% 2.22/1.03  abstr_ref_over_cycles:                  0
% 2.22/1.03  abstr_ref_under_cycles:                 0
% 2.22/1.03  gc_basic_clause_elim:                   0
% 2.22/1.03  forced_gc_time:                         0
% 2.22/1.03  parsing_time:                           0.011
% 2.22/1.03  unif_index_cands_time:                  0.
% 2.22/1.03  unif_index_add_time:                    0.
% 2.22/1.03  orderings_time:                         0.
% 2.22/1.03  out_proof_time:                         0.013
% 2.22/1.03  total_time:                             0.188
% 2.22/1.03  num_of_symbols:                         59
% 2.22/1.03  num_of_terms:                           2822
% 2.22/1.03  
% 2.22/1.03  ------ Preprocessing
% 2.22/1.03  
% 2.22/1.03  num_of_splits:                          0
% 2.22/1.03  num_of_split_atoms:                     0
% 2.22/1.03  num_of_reused_defs:                     0
% 2.22/1.03  num_eq_ax_congr_red:                    24
% 2.22/1.03  num_of_sem_filtered_clauses:            1
% 2.22/1.03  num_of_subtypes:                        3
% 2.22/1.03  monotx_restored_types:                  0
% 2.22/1.03  sat_num_of_epr_types:                   0
% 2.22/1.03  sat_num_of_non_cyclic_types:            0
% 2.22/1.03  sat_guarded_non_collapsed_types:        0
% 2.22/1.03  num_pure_diseq_elim:                    0
% 2.22/1.03  simp_replaced_by:                       0
% 2.22/1.03  res_preprocessed:                       162
% 2.22/1.03  prep_upred:                             0
% 2.22/1.03  prep_unflattend:                        23
% 2.22/1.03  smt_new_axioms:                         0
% 2.22/1.03  pred_elim_cands:                        8
% 2.22/1.03  pred_elim:                              3
% 2.22/1.03  pred_elim_cl:                           3
% 2.22/1.03  pred_elim_cycles:                       5
% 2.22/1.03  merged_defs:                            16
% 2.22/1.03  merged_defs_ncl:                        0
% 2.22/1.03  bin_hyper_res:                          16
% 2.22/1.03  prep_cycles:                            4
% 2.22/1.03  pred_elim_time:                         0.035
% 2.22/1.03  splitting_time:                         0.
% 2.22/1.03  sem_filter_time:                        0.
% 2.22/1.03  monotx_time:                            0.
% 2.22/1.03  subtype_inf_time:                       0.
% 2.22/1.03  
% 2.22/1.03  ------ Problem properties
% 2.22/1.03  
% 2.22/1.03  clauses:                                33
% 2.22/1.03  conjectures:                            20
% 2.22/1.03  epr:                                    16
% 2.22/1.03  horn:                                   27
% 2.22/1.03  ground:                                 20
% 2.22/1.03  unary:                                  18
% 2.22/1.03  binary:                                 5
% 2.22/1.03  lits:                                   126
% 2.22/1.03  lits_eq:                                13
% 2.22/1.03  fd_pure:                                0
% 2.22/1.03  fd_pseudo:                              0
% 2.22/1.03  fd_cond:                                0
% 2.22/1.03  fd_pseudo_cond:                         0
% 2.22/1.03  ac_symbols:                             0
% 2.22/1.03  
% 2.22/1.03  ------ Propositional Solver
% 2.22/1.03  
% 2.22/1.03  prop_solver_calls:                      29
% 2.22/1.03  prop_fast_solver_calls:                 1893
% 2.22/1.03  smt_solver_calls:                       0
% 2.22/1.03  smt_fast_solver_calls:                  0
% 2.22/1.03  prop_num_of_clauses:                    1103
% 2.22/1.03  prop_preprocess_simplified:             4660
% 2.22/1.03  prop_fo_subsumed:                       33
% 2.22/1.03  prop_solver_time:                       0.
% 2.22/1.03  smt_solver_time:                        0.
% 2.22/1.03  smt_fast_solver_time:                   0.
% 2.22/1.03  prop_fast_solver_time:                  0.
% 2.22/1.03  prop_unsat_core_time:                   0.
% 2.22/1.03  
% 2.22/1.03  ------ QBF
% 2.22/1.03  
% 2.22/1.03  qbf_q_res:                              0
% 2.22/1.03  qbf_num_tautologies:                    0
% 2.22/1.03  qbf_prep_cycles:                        0
% 2.22/1.03  
% 2.22/1.03  ------ BMC1
% 2.22/1.03  
% 2.22/1.03  bmc1_current_bound:                     -1
% 2.22/1.03  bmc1_last_solved_bound:                 -1
% 2.22/1.03  bmc1_unsat_core_size:                   -1
% 2.22/1.03  bmc1_unsat_core_parents_size:           -1
% 2.22/1.03  bmc1_merge_next_fun:                    0
% 2.22/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.22/1.03  
% 2.22/1.03  ------ Instantiation
% 2.22/1.03  
% 2.22/1.03  inst_num_of_clauses:                    321
% 2.22/1.03  inst_num_in_passive:                    30
% 2.22/1.03  inst_num_in_active:                     277
% 2.22/1.03  inst_num_in_unprocessed:                13
% 2.22/1.03  inst_num_of_loops:                      310
% 2.22/1.03  inst_num_of_learning_restarts:          0
% 2.22/1.03  inst_num_moves_active_passive:          26
% 2.22/1.03  inst_lit_activity:                      0
% 2.22/1.03  inst_lit_activity_moves:                0
% 2.22/1.03  inst_num_tautologies:                   0
% 2.22/1.03  inst_num_prop_implied:                  0
% 2.22/1.03  inst_num_existing_simplified:           0
% 2.22/1.03  inst_num_eq_res_simplified:             0
% 2.22/1.03  inst_num_child_elim:                    0
% 2.22/1.03  inst_num_of_dismatching_blockings:      34
% 2.22/1.03  inst_num_of_non_proper_insts:           371
% 2.22/1.03  inst_num_of_duplicates:                 0
% 2.22/1.03  inst_inst_num_from_inst_to_res:         0
% 2.22/1.03  inst_dismatching_checking_time:         0.
% 2.22/1.03  
% 2.22/1.03  ------ Resolution
% 2.22/1.03  
% 2.22/1.03  res_num_of_clauses:                     0
% 2.22/1.03  res_num_in_passive:                     0
% 2.22/1.03  res_num_in_active:                      0
% 2.22/1.03  res_num_of_loops:                       166
% 2.22/1.03  res_forward_subset_subsumed:            87
% 2.22/1.03  res_backward_subset_subsumed:           0
% 2.22/1.03  res_forward_subsumed:                   0
% 2.22/1.03  res_backward_subsumed:                  0
% 2.22/1.03  res_forward_subsumption_resolution:     6
% 2.22/1.03  res_backward_subsumption_resolution:    0
% 2.22/1.03  res_clause_to_clause_subsumption:       422
% 2.22/1.03  res_orphan_elimination:                 0
% 2.22/1.03  res_tautology_del:                      116
% 2.22/1.03  res_num_eq_res_simplified:              0
% 2.22/1.03  res_num_sel_changes:                    0
% 2.22/1.03  res_moves_from_active_to_pass:          0
% 2.22/1.03  
% 2.22/1.03  ------ Superposition
% 2.22/1.03  
% 2.22/1.03  sup_time_total:                         0.
% 2.22/1.03  sup_time_generating:                    0.
% 2.22/1.03  sup_time_sim_full:                      0.
% 2.22/1.03  sup_time_sim_immed:                     0.
% 2.22/1.03  
% 2.22/1.03  sup_num_of_clauses:                     72
% 2.22/1.03  sup_num_in_active:                      60
% 2.22/1.03  sup_num_in_passive:                     12
% 2.22/1.03  sup_num_of_loops:                       60
% 2.22/1.03  sup_fw_superposition:                   34
% 2.22/1.03  sup_bw_superposition:                   20
% 2.22/1.03  sup_immediate_simplified:               6
% 2.22/1.03  sup_given_eliminated:                   0
% 2.22/1.03  comparisons_done:                       0
% 2.22/1.03  comparisons_avoided:                    0
% 2.22/1.03  
% 2.22/1.03  ------ Simplifications
% 2.22/1.03  
% 2.22/1.03  
% 2.22/1.03  sim_fw_subset_subsumed:                 6
% 2.22/1.03  sim_bw_subset_subsumed:                 0
% 2.22/1.03  sim_fw_subsumed:                        0
% 2.22/1.03  sim_bw_subsumed:                        0
% 2.22/1.03  sim_fw_subsumption_res:                 3
% 2.22/1.03  sim_bw_subsumption_res:                 0
% 2.22/1.03  sim_tautology_del:                      2
% 2.22/1.03  sim_eq_tautology_del:                   0
% 2.22/1.03  sim_eq_res_simp:                        0
% 2.22/1.03  sim_fw_demodulated:                     0
% 2.22/1.03  sim_bw_demodulated:                     0
% 2.22/1.03  sim_light_normalised:                   6
% 2.22/1.03  sim_joinable_taut:                      0
% 2.22/1.03  sim_joinable_simp:                      0
% 2.22/1.03  sim_ac_normalised:                      0
% 2.22/1.03  sim_smt_subsumption:                    0
% 2.22/1.03  
%------------------------------------------------------------------------------
