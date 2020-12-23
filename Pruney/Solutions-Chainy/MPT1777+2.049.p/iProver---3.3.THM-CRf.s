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
% DateTime   : Thu Dec  3 12:23:34 EST 2020

% Result     : Theorem 15.54s
% Output     : CNFRefutation 15.54s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 460 expanded)
%              Number of clauses        :   82 (  96 expanded)
%              Number of leaves         :   21 ( 204 expanded)
%              Depth                    :   13
%              Number of atoms          :  808 (6378 expanded)
%              Number of equality atoms :   87 ( 841 expanded)
%              Maximal formula depth    :   31 (   6 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f29])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
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
    inference(equality_resolution,[],[f64])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
    inference(flattening,[],[f31])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X3,X1,X4,X5)
          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X3,X1,X4,X5)
        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7)
        & sK7 = X5
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(X3,X1,X4,X5)
              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ~ r1_tmap_1(X3,X1,X4,sK6)
            & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            & sK6 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(X3,X1,X4,X5)
                  & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(X3,X1,sK5,X5)
                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,X1,X4,X5)
                      & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(sK4,X1,X4,X5)
                    & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK4)) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK4
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,X1,X4,X5)
                          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
                        ( ~ r1_tmap_1(X3,X1,X4,X5)
                        & r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK3)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
                            ( ~ r1_tmap_1(X3,sK2,X4,X5)
                            & r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X3,X1,X4,X5)
                                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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

fof(f47,plain,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK6)
    & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK3))
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f32,f46,f45,f44,f43,f42,f41,f40])).

fof(f78,plain,(
    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK0(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f37])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f47])).

fof(f83,plain,(
    ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f69,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f68,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f66,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f65,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_591,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_7026,plain,
    ( ~ r1_tarski(sK0(sK4,sK6),X0)
    | r1_tarski(sK0(sK4,sK6),X1)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_591])).

cnf(c_17112,plain,
    ( r1_tarski(sK0(sK4,sK6),X0)
    | ~ r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4))
    | X0 != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_7026])).

cnf(c_72367,plain,
    ( r1_tarski(sK0(sK4,sK6),u1_struct_0(sK3))
    | ~ r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4))
    | u1_struct_0(sK3) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_17112])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2914,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(X0))
    | r1_tarski(u1_struct_0(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3969,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(X0)))
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2914])).

cnf(c_32566,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3969])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2423,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),X0)
    | u1_struct_0(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_19870,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK3))
    | u1_struct_0(sK3) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2423])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3970,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_15669,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_3970])).

cnf(c_2338,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0))
    | r1_tarski(u1_struct_0(sK3),X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3694,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2338])).

cnf(c_10990,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3694])).

cnf(c_7015,plain,
    ( ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(X0))
    | r1_tarski(sK0(sK4,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_10946,plain,
    ( ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_7015])).

cnf(c_3695,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_8372,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_3695])).

cnf(c_15,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3133,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,X3),sK6)
    | r1_tmap_1(sK4,X1,X3,sK6)
    | ~ v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_connsp_2(sK0(sK4,sK6),sK4,sK6)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r1_tarski(sK0(sK4,sK6),u1_struct_0(X0))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_4851,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),sK6)
    | r1_tmap_1(sK4,X1,sK5,sK6)
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_connsp_2(sK0(sK4,sK6),sK4,sK6)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,X2)
    | ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ r1_tarski(sK0(sK4,sK6),u1_struct_0(X0))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(instantiation,[status(thm)],[c_3133])).

cnf(c_6813,plain,
    ( ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)
    | r1_tmap_1(sK4,sK2,sK5,sK6)
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_connsp_2(sK0(sK4,sK6),sK4,sK6)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ r1_tarski(sK0(sK4,sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_4851])).

cnf(c_13,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1422,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_22,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1424,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3034,plain,
    ( m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK4,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1424])).

cnf(c_3192,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_3034])).

cnf(c_3209,plain,
    ( m1_pre_topc(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3192])).

cnf(c_9,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3124,plain,
    ( ~ m1_connsp_2(sK0(sK4,sK6),sK4,sK6)
    | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_326,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_6])).

cnf(c_327,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_326])).

cnf(c_1401,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_327])).

cnf(c_1756,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1401])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_38,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_43,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1866,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2013,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1866])).

cnf(c_2014,plain,
    ( m1_pre_topc(sK3,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2013])).

cnf(c_3020,plain,
    ( m1_pre_topc(X0,sK4) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1756,c_38,c_43,c_2014])).

cnf(c_3021,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3020])).

cnf(c_3028,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_3021])).

cnf(c_3029,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3028])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2123,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2693,plain,
    ( ~ m1_pre_topc(sK4,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_2123])).

cnf(c_1876,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2069,plain,
    ( ~ m1_pre_topc(sK4,sK1)
    | ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1876])).

cnf(c_10,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1829,plain,
    ( m1_connsp_2(sK0(sK4,sK6),sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1416,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1462,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1416,c_19])).

cnf(c_1679,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1462])).

cnf(c_18,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1417,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1477,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1417,c_19])).

cnf(c_1673,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1477])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_72367,c_32566,c_19870,c_15669,c_10990,c_10946,c_8372,c_6813,c_3209,c_3124,c_3029,c_2693,c_2069,c_2013,c_1829,c_1679,c_1673,c_17,c_21,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.54/2.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.54/2.51  
% 15.54/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.54/2.51  
% 15.54/2.51  ------  iProver source info
% 15.54/2.51  
% 15.54/2.51  git: date: 2020-06-30 10:37:57 +0100
% 15.54/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.54/2.51  git: non_committed_changes: false
% 15.54/2.51  git: last_make_outside_of_git: false
% 15.54/2.51  
% 15.54/2.51  ------ 
% 15.54/2.51  
% 15.54/2.51  ------ Input Options
% 15.54/2.51  
% 15.54/2.51  --out_options                           all
% 15.54/2.51  --tptp_safe_out                         true
% 15.54/2.51  --problem_path                          ""
% 15.54/2.51  --include_path                          ""
% 15.54/2.51  --clausifier                            res/vclausify_rel
% 15.54/2.51  --clausifier_options                    --mode clausify
% 15.54/2.51  --stdin                                 false
% 15.54/2.51  --stats_out                             sel
% 15.54/2.51  
% 15.54/2.51  ------ General Options
% 15.54/2.51  
% 15.54/2.51  --fof                                   false
% 15.54/2.51  --time_out_real                         604.99
% 15.54/2.51  --time_out_virtual                      -1.
% 15.54/2.51  --symbol_type_check                     false
% 15.54/2.51  --clausify_out                          false
% 15.54/2.51  --sig_cnt_out                           false
% 15.54/2.51  --trig_cnt_out                          false
% 15.54/2.51  --trig_cnt_out_tolerance                1.
% 15.54/2.51  --trig_cnt_out_sk_spl                   false
% 15.54/2.51  --abstr_cl_out                          false
% 15.54/2.51  
% 15.54/2.51  ------ Global Options
% 15.54/2.51  
% 15.54/2.51  --schedule                              none
% 15.54/2.51  --add_important_lit                     false
% 15.54/2.51  --prop_solver_per_cl                    1000
% 15.54/2.51  --min_unsat_core                        false
% 15.54/2.51  --soft_assumptions                      false
% 15.54/2.51  --soft_lemma_size                       3
% 15.54/2.51  --prop_impl_unit_size                   0
% 15.54/2.51  --prop_impl_unit                        []
% 15.54/2.51  --share_sel_clauses                     true
% 15.54/2.51  --reset_solvers                         false
% 15.54/2.51  --bc_imp_inh                            [conj_cone]
% 15.54/2.51  --conj_cone_tolerance                   3.
% 15.54/2.51  --extra_neg_conj                        none
% 15.54/2.51  --large_theory_mode                     true
% 15.54/2.51  --prolific_symb_bound                   200
% 15.54/2.51  --lt_threshold                          2000
% 15.54/2.51  --clause_weak_htbl                      true
% 15.54/2.51  --gc_record_bc_elim                     false
% 15.54/2.51  
% 15.54/2.51  ------ Preprocessing Options
% 15.54/2.51  
% 15.54/2.51  --preprocessing_flag                    true
% 15.54/2.51  --time_out_prep_mult                    0.1
% 15.54/2.51  --splitting_mode                        input
% 15.54/2.51  --splitting_grd                         true
% 15.54/2.51  --splitting_cvd                         false
% 15.54/2.51  --splitting_cvd_svl                     false
% 15.54/2.51  --splitting_nvd                         32
% 15.54/2.51  --sub_typing                            true
% 15.54/2.51  --prep_gs_sim                           false
% 15.54/2.51  --prep_unflatten                        true
% 15.54/2.51  --prep_res_sim                          true
% 15.54/2.51  --prep_upred                            true
% 15.54/2.51  --prep_sem_filter                       exhaustive
% 15.54/2.51  --prep_sem_filter_out                   false
% 15.54/2.51  --pred_elim                             false
% 15.54/2.51  --res_sim_input                         true
% 15.54/2.51  --eq_ax_congr_red                       true
% 15.54/2.51  --pure_diseq_elim                       true
% 15.54/2.51  --brand_transform                       false
% 15.54/2.51  --non_eq_to_eq                          false
% 15.54/2.51  --prep_def_merge                        true
% 15.54/2.51  --prep_def_merge_prop_impl              false
% 15.54/2.51  --prep_def_merge_mbd                    true
% 15.54/2.51  --prep_def_merge_tr_red                 false
% 15.54/2.51  --prep_def_merge_tr_cl                  false
% 15.54/2.51  --smt_preprocessing                     true
% 15.54/2.51  --smt_ac_axioms                         fast
% 15.54/2.51  --preprocessed_out                      false
% 15.54/2.51  --preprocessed_stats                    false
% 15.54/2.51  
% 15.54/2.51  ------ Abstraction refinement Options
% 15.54/2.51  
% 15.54/2.51  --abstr_ref                             []
% 15.54/2.51  --abstr_ref_prep                        false
% 15.54/2.51  --abstr_ref_until_sat                   false
% 15.54/2.51  --abstr_ref_sig_restrict                funpre
% 15.54/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.54/2.51  --abstr_ref_under                       []
% 15.54/2.51  
% 15.54/2.51  ------ SAT Options
% 15.54/2.51  
% 15.54/2.51  --sat_mode                              false
% 15.54/2.51  --sat_fm_restart_options                ""
% 15.54/2.51  --sat_gr_def                            false
% 15.54/2.51  --sat_epr_types                         true
% 15.54/2.51  --sat_non_cyclic_types                  false
% 15.54/2.51  --sat_finite_models                     false
% 15.54/2.51  --sat_fm_lemmas                         false
% 15.54/2.51  --sat_fm_prep                           false
% 15.54/2.51  --sat_fm_uc_incr                        true
% 15.54/2.51  --sat_out_model                         small
% 15.54/2.51  --sat_out_clauses                       false
% 15.54/2.51  
% 15.54/2.51  ------ QBF Options
% 15.54/2.51  
% 15.54/2.51  --qbf_mode                              false
% 15.54/2.51  --qbf_elim_univ                         false
% 15.54/2.51  --qbf_dom_inst                          none
% 15.54/2.51  --qbf_dom_pre_inst                      false
% 15.54/2.51  --qbf_sk_in                             false
% 15.54/2.51  --qbf_pred_elim                         true
% 15.54/2.51  --qbf_split                             512
% 15.54/2.51  
% 15.54/2.51  ------ BMC1 Options
% 15.54/2.51  
% 15.54/2.51  --bmc1_incremental                      false
% 15.54/2.51  --bmc1_axioms                           reachable_all
% 15.54/2.51  --bmc1_min_bound                        0
% 15.54/2.51  --bmc1_max_bound                        -1
% 15.54/2.51  --bmc1_max_bound_default                -1
% 15.54/2.51  --bmc1_symbol_reachability              true
% 15.54/2.51  --bmc1_property_lemmas                  false
% 15.54/2.51  --bmc1_k_induction                      false
% 15.54/2.51  --bmc1_non_equiv_states                 false
% 15.54/2.51  --bmc1_deadlock                         false
% 15.54/2.51  --bmc1_ucm                              false
% 15.54/2.51  --bmc1_add_unsat_core                   none
% 15.54/2.51  --bmc1_unsat_core_children              false
% 15.54/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.54/2.51  --bmc1_out_stat                         full
% 15.54/2.51  --bmc1_ground_init                      false
% 15.54/2.51  --bmc1_pre_inst_next_state              false
% 15.54/2.51  --bmc1_pre_inst_state                   false
% 15.54/2.51  --bmc1_pre_inst_reach_state             false
% 15.54/2.51  --bmc1_out_unsat_core                   false
% 15.54/2.51  --bmc1_aig_witness_out                  false
% 15.54/2.51  --bmc1_verbose                          false
% 15.54/2.51  --bmc1_dump_clauses_tptp                false
% 15.54/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.54/2.51  --bmc1_dump_file                        -
% 15.54/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.54/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.54/2.51  --bmc1_ucm_extend_mode                  1
% 15.54/2.51  --bmc1_ucm_init_mode                    2
% 15.54/2.51  --bmc1_ucm_cone_mode                    none
% 15.54/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.54/2.51  --bmc1_ucm_relax_model                  4
% 15.54/2.51  --bmc1_ucm_full_tr_after_sat            true
% 15.54/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 15.54/2.51  --bmc1_ucm_layered_model                none
% 15.54/2.51  --bmc1_ucm_max_lemma_size               10
% 15.54/2.51  
% 15.54/2.51  ------ AIG Options
% 15.54/2.51  
% 15.54/2.51  --aig_mode                              false
% 15.54/2.51  
% 15.54/2.51  ------ Instantiation Options
% 15.54/2.51  
% 15.54/2.51  --instantiation_flag                    true
% 15.54/2.51  --inst_sos_flag                         false
% 15.54/2.51  --inst_sos_phase                        true
% 15.54/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.54/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.54/2.51  --inst_lit_sel_side                     num_symb
% 15.54/2.51  --inst_solver_per_active                1400
% 15.54/2.51  --inst_solver_calls_frac                1.
% 15.54/2.51  --inst_passive_queue_type               priority_queues
% 15.54/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.54/2.51  --inst_passive_queues_freq              [25;2]
% 15.54/2.51  --inst_dismatching                      true
% 15.54/2.51  --inst_eager_unprocessed_to_passive     true
% 15.54/2.51  --inst_prop_sim_given                   true
% 15.54/2.51  --inst_prop_sim_new                     false
% 15.54/2.51  --inst_subs_new                         false
% 15.54/2.51  --inst_eq_res_simp                      false
% 15.54/2.51  --inst_subs_given                       false
% 15.54/2.51  --inst_orphan_elimination               true
% 15.54/2.51  --inst_learning_loop_flag               true
% 15.54/2.51  --inst_learning_start                   3000
% 15.54/2.51  --inst_learning_factor                  2
% 15.54/2.51  --inst_start_prop_sim_after_learn       3
% 15.54/2.51  --inst_sel_renew                        solver
% 15.54/2.51  --inst_lit_activity_flag                true
% 15.54/2.51  --inst_restr_to_given                   false
% 15.54/2.51  --inst_activity_threshold               500
% 15.54/2.51  --inst_out_proof                        true
% 15.54/2.51  
% 15.54/2.51  ------ Resolution Options
% 15.54/2.51  
% 15.54/2.51  --resolution_flag                       true
% 15.54/2.51  --res_lit_sel                           adaptive
% 15.54/2.51  --res_lit_sel_side                      none
% 15.54/2.51  --res_ordering                          kbo
% 15.54/2.51  --res_to_prop_solver                    active
% 15.54/2.51  --res_prop_simpl_new                    false
% 15.54/2.51  --res_prop_simpl_given                  true
% 15.54/2.51  --res_passive_queue_type                priority_queues
% 15.54/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.54/2.51  --res_passive_queues_freq               [15;5]
% 15.54/2.51  --res_forward_subs                      full
% 15.54/2.51  --res_backward_subs                     full
% 15.54/2.51  --res_forward_subs_resolution           true
% 15.54/2.51  --res_backward_subs_resolution          true
% 15.54/2.51  --res_orphan_elimination                true
% 15.54/2.51  --res_time_limit                        2.
% 15.54/2.51  --res_out_proof                         true
% 15.54/2.51  
% 15.54/2.51  ------ Superposition Options
% 15.54/2.51  
% 15.54/2.51  --superposition_flag                    true
% 15.54/2.51  --sup_passive_queue_type                priority_queues
% 15.54/2.51  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.54/2.51  --sup_passive_queues_freq               [1;4]
% 15.54/2.51  --demod_completeness_check              fast
% 15.54/2.51  --demod_use_ground                      true
% 15.54/2.51  --sup_to_prop_solver                    passive
% 15.54/2.51  --sup_prop_simpl_new                    true
% 15.54/2.51  --sup_prop_simpl_given                  true
% 15.54/2.51  --sup_fun_splitting                     false
% 15.54/2.51  --sup_smt_interval                      50000
% 15.54/2.51  
% 15.54/2.51  ------ Superposition Simplification Setup
% 15.54/2.51  
% 15.54/2.51  --sup_indices_passive                   []
% 15.54/2.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.54/2.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.54/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.54/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.54/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.54/2.51  --sup_full_bw                           [BwDemod]
% 15.54/2.51  --sup_immed_triv                        [TrivRules]
% 15.54/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.54/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.54/2.51  --sup_immed_bw_main                     []
% 15.54/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.54/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.54/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.54/2.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.54/2.51  
% 15.54/2.51  ------ Combination Options
% 15.54/2.51  
% 15.54/2.51  --comb_res_mult                         3
% 15.54/2.51  --comb_sup_mult                         2
% 15.54/2.51  --comb_inst_mult                        10
% 15.54/2.51  
% 15.54/2.51  ------ Debug Options
% 15.54/2.51  
% 15.54/2.51  --dbg_backtrace                         false
% 15.54/2.51  --dbg_dump_prop_clauses                 false
% 15.54/2.51  --dbg_dump_prop_clauses_file            -
% 15.54/2.51  --dbg_out_stat                          false
% 15.54/2.51  ------ Parsing...
% 15.54/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.54/2.51  
% 15.54/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.54/2.51  
% 15.54/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.54/2.51  
% 15.54/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.54/2.51  ------ Proving...
% 15.54/2.51  ------ Problem Properties 
% 15.54/2.51  
% 15.54/2.51  
% 15.54/2.51  clauses                                 35
% 15.54/2.51  conjectures                             19
% 15.54/2.51  EPR                                     19
% 15.54/2.51  Horn                                    31
% 15.54/2.51  unary                                   20
% 15.54/2.51  binary                                  3
% 15.54/2.51  lits                                    107
% 15.54/2.51  lits eq                                 3
% 15.54/2.51  fd_pure                                 0
% 15.54/2.51  fd_pseudo                               0
% 15.54/2.51  fd_cond                                 0
% 15.54/2.51  fd_pseudo_cond                          1
% 15.54/2.51  AC symbols                              0
% 15.54/2.51  
% 15.54/2.51  ------ Input Options Time Limit: Unbounded
% 15.54/2.51  
% 15.54/2.51  
% 15.54/2.51  ------ 
% 15.54/2.51  Current options:
% 15.54/2.51  ------ 
% 15.54/2.51  
% 15.54/2.51  ------ Input Options
% 15.54/2.51  
% 15.54/2.51  --out_options                           all
% 15.54/2.51  --tptp_safe_out                         true
% 15.54/2.51  --problem_path                          ""
% 15.54/2.51  --include_path                          ""
% 15.54/2.51  --clausifier                            res/vclausify_rel
% 15.54/2.51  --clausifier_options                    --mode clausify
% 15.54/2.51  --stdin                                 false
% 15.54/2.51  --stats_out                             sel
% 15.54/2.51  
% 15.54/2.51  ------ General Options
% 15.54/2.51  
% 15.54/2.51  --fof                                   false
% 15.54/2.51  --time_out_real                         604.99
% 15.54/2.51  --time_out_virtual                      -1.
% 15.54/2.51  --symbol_type_check                     false
% 15.54/2.51  --clausify_out                          false
% 15.54/2.51  --sig_cnt_out                           false
% 15.54/2.51  --trig_cnt_out                          false
% 15.54/2.51  --trig_cnt_out_tolerance                1.
% 15.54/2.51  --trig_cnt_out_sk_spl                   false
% 15.54/2.51  --abstr_cl_out                          false
% 15.54/2.51  
% 15.54/2.51  ------ Global Options
% 15.54/2.51  
% 15.54/2.51  --schedule                              none
% 15.54/2.51  --add_important_lit                     false
% 15.54/2.51  --prop_solver_per_cl                    1000
% 15.54/2.51  --min_unsat_core                        false
% 15.54/2.51  --soft_assumptions                      false
% 15.54/2.51  --soft_lemma_size                       3
% 15.54/2.51  --prop_impl_unit_size                   0
% 15.54/2.51  --prop_impl_unit                        []
% 15.54/2.51  --share_sel_clauses                     true
% 15.54/2.51  --reset_solvers                         false
% 15.54/2.51  --bc_imp_inh                            [conj_cone]
% 15.54/2.51  --conj_cone_tolerance                   3.
% 15.54/2.51  --extra_neg_conj                        none
% 15.54/2.51  --large_theory_mode                     true
% 15.54/2.51  --prolific_symb_bound                   200
% 15.54/2.51  --lt_threshold                          2000
% 15.54/2.51  --clause_weak_htbl                      true
% 15.54/2.51  --gc_record_bc_elim                     false
% 15.54/2.51  
% 15.54/2.51  ------ Preprocessing Options
% 15.54/2.51  
% 15.54/2.51  --preprocessing_flag                    true
% 15.54/2.51  --time_out_prep_mult                    0.1
% 15.54/2.51  --splitting_mode                        input
% 15.54/2.51  --splitting_grd                         true
% 15.54/2.51  --splitting_cvd                         false
% 15.54/2.51  --splitting_cvd_svl                     false
% 15.54/2.51  --splitting_nvd                         32
% 15.54/2.51  --sub_typing                            true
% 15.54/2.51  --prep_gs_sim                           false
% 15.54/2.51  --prep_unflatten                        true
% 15.54/2.51  --prep_res_sim                          true
% 15.54/2.51  --prep_upred                            true
% 15.54/2.51  --prep_sem_filter                       exhaustive
% 15.54/2.51  --prep_sem_filter_out                   false
% 15.54/2.51  --pred_elim                             false
% 15.54/2.51  --res_sim_input                         true
% 15.54/2.51  --eq_ax_congr_red                       true
% 15.54/2.51  --pure_diseq_elim                       true
% 15.54/2.51  --brand_transform                       false
% 15.54/2.51  --non_eq_to_eq                          false
% 15.54/2.51  --prep_def_merge                        true
% 15.54/2.51  --prep_def_merge_prop_impl              false
% 15.54/2.51  --prep_def_merge_mbd                    true
% 15.54/2.51  --prep_def_merge_tr_red                 false
% 15.54/2.51  --prep_def_merge_tr_cl                  false
% 15.54/2.51  --smt_preprocessing                     true
% 15.54/2.51  --smt_ac_axioms                         fast
% 15.54/2.51  --preprocessed_out                      false
% 15.54/2.51  --preprocessed_stats                    false
% 15.54/2.51  
% 15.54/2.51  ------ Abstraction refinement Options
% 15.54/2.51  
% 15.54/2.51  --abstr_ref                             []
% 15.54/2.51  --abstr_ref_prep                        false
% 15.54/2.51  --abstr_ref_until_sat                   false
% 15.54/2.51  --abstr_ref_sig_restrict                funpre
% 15.54/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.54/2.51  --abstr_ref_under                       []
% 15.54/2.51  
% 15.54/2.51  ------ SAT Options
% 15.54/2.51  
% 15.54/2.51  --sat_mode                              false
% 15.54/2.51  --sat_fm_restart_options                ""
% 15.54/2.51  --sat_gr_def                            false
% 15.54/2.51  --sat_epr_types                         true
% 15.54/2.51  --sat_non_cyclic_types                  false
% 15.54/2.51  --sat_finite_models                     false
% 15.54/2.51  --sat_fm_lemmas                         false
% 15.54/2.51  --sat_fm_prep                           false
% 15.54/2.51  --sat_fm_uc_incr                        true
% 15.54/2.51  --sat_out_model                         small
% 15.54/2.51  --sat_out_clauses                       false
% 15.54/2.51  
% 15.54/2.51  ------ QBF Options
% 15.54/2.51  
% 15.54/2.51  --qbf_mode                              false
% 15.54/2.51  --qbf_elim_univ                         false
% 15.54/2.51  --qbf_dom_inst                          none
% 15.54/2.51  --qbf_dom_pre_inst                      false
% 15.54/2.51  --qbf_sk_in                             false
% 15.54/2.51  --qbf_pred_elim                         true
% 15.54/2.51  --qbf_split                             512
% 15.54/2.51  
% 15.54/2.51  ------ BMC1 Options
% 15.54/2.51  
% 15.54/2.51  --bmc1_incremental                      false
% 15.54/2.51  --bmc1_axioms                           reachable_all
% 15.54/2.51  --bmc1_min_bound                        0
% 15.54/2.51  --bmc1_max_bound                        -1
% 15.54/2.51  --bmc1_max_bound_default                -1
% 15.54/2.51  --bmc1_symbol_reachability              true
% 15.54/2.51  --bmc1_property_lemmas                  false
% 15.54/2.51  --bmc1_k_induction                      false
% 15.54/2.51  --bmc1_non_equiv_states                 false
% 15.54/2.51  --bmc1_deadlock                         false
% 15.54/2.51  --bmc1_ucm                              false
% 15.54/2.51  --bmc1_add_unsat_core                   none
% 15.54/2.51  --bmc1_unsat_core_children              false
% 15.54/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.54/2.51  --bmc1_out_stat                         full
% 15.54/2.51  --bmc1_ground_init                      false
% 15.54/2.51  --bmc1_pre_inst_next_state              false
% 15.54/2.51  --bmc1_pre_inst_state                   false
% 15.54/2.51  --bmc1_pre_inst_reach_state             false
% 15.54/2.51  --bmc1_out_unsat_core                   false
% 15.54/2.51  --bmc1_aig_witness_out                  false
% 15.54/2.51  --bmc1_verbose                          false
% 15.54/2.51  --bmc1_dump_clauses_tptp                false
% 15.54/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.54/2.51  --bmc1_dump_file                        -
% 15.54/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.54/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.54/2.51  --bmc1_ucm_extend_mode                  1
% 15.54/2.51  --bmc1_ucm_init_mode                    2
% 15.54/2.51  --bmc1_ucm_cone_mode                    none
% 15.54/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.54/2.51  --bmc1_ucm_relax_model                  4
% 15.54/2.51  --bmc1_ucm_full_tr_after_sat            true
% 15.54/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 15.54/2.51  --bmc1_ucm_layered_model                none
% 15.54/2.51  --bmc1_ucm_max_lemma_size               10
% 15.54/2.51  
% 15.54/2.51  ------ AIG Options
% 15.54/2.51  
% 15.54/2.51  --aig_mode                              false
% 15.54/2.51  
% 15.54/2.51  ------ Instantiation Options
% 15.54/2.51  
% 15.54/2.51  --instantiation_flag                    true
% 15.54/2.51  --inst_sos_flag                         false
% 15.54/2.51  --inst_sos_phase                        true
% 15.54/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.54/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.54/2.51  --inst_lit_sel_side                     num_symb
% 15.54/2.51  --inst_solver_per_active                1400
% 15.54/2.51  --inst_solver_calls_frac                1.
% 15.54/2.51  --inst_passive_queue_type               priority_queues
% 15.54/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.54/2.51  --inst_passive_queues_freq              [25;2]
% 15.54/2.51  --inst_dismatching                      true
% 15.54/2.51  --inst_eager_unprocessed_to_passive     true
% 15.54/2.51  --inst_prop_sim_given                   true
% 15.54/2.51  --inst_prop_sim_new                     false
% 15.54/2.51  --inst_subs_new                         false
% 15.54/2.51  --inst_eq_res_simp                      false
% 15.54/2.51  --inst_subs_given                       false
% 15.54/2.51  --inst_orphan_elimination               true
% 15.54/2.51  --inst_learning_loop_flag               true
% 15.54/2.51  --inst_learning_start                   3000
% 15.54/2.51  --inst_learning_factor                  2
% 15.54/2.51  --inst_start_prop_sim_after_learn       3
% 15.54/2.51  --inst_sel_renew                        solver
% 15.54/2.51  --inst_lit_activity_flag                true
% 15.54/2.51  --inst_restr_to_given                   false
% 15.54/2.51  --inst_activity_threshold               500
% 15.54/2.51  --inst_out_proof                        true
% 15.54/2.51  
% 15.54/2.51  ------ Resolution Options
% 15.54/2.51  
% 15.54/2.51  --resolution_flag                       true
% 15.54/2.51  --res_lit_sel                           adaptive
% 15.54/2.51  --res_lit_sel_side                      none
% 15.54/2.51  --res_ordering                          kbo
% 15.54/2.51  --res_to_prop_solver                    active
% 15.54/2.51  --res_prop_simpl_new                    false
% 15.54/2.51  --res_prop_simpl_given                  true
% 15.54/2.51  --res_passive_queue_type                priority_queues
% 15.54/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.54/2.51  --res_passive_queues_freq               [15;5]
% 15.54/2.51  --res_forward_subs                      full
% 15.54/2.51  --res_backward_subs                     full
% 15.54/2.51  --res_forward_subs_resolution           true
% 15.54/2.51  --res_backward_subs_resolution          true
% 15.54/2.51  --res_orphan_elimination                true
% 15.54/2.51  --res_time_limit                        2.
% 15.54/2.51  --res_out_proof                         true
% 15.54/2.51  
% 15.54/2.51  ------ Superposition Options
% 15.54/2.51  
% 15.54/2.51  --superposition_flag                    true
% 15.54/2.51  --sup_passive_queue_type                priority_queues
% 15.54/2.51  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.54/2.51  --sup_passive_queues_freq               [1;4]
% 15.54/2.51  --demod_completeness_check              fast
% 15.54/2.51  --demod_use_ground                      true
% 15.54/2.51  --sup_to_prop_solver                    passive
% 15.54/2.51  --sup_prop_simpl_new                    true
% 15.54/2.51  --sup_prop_simpl_given                  true
% 15.54/2.51  --sup_fun_splitting                     false
% 15.54/2.51  --sup_smt_interval                      50000
% 15.54/2.51  
% 15.54/2.51  ------ Superposition Simplification Setup
% 15.54/2.51  
% 15.54/2.51  --sup_indices_passive                   []
% 15.54/2.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.54/2.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.54/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.54/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.54/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.54/2.51  --sup_full_bw                           [BwDemod]
% 15.54/2.51  --sup_immed_triv                        [TrivRules]
% 15.54/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.54/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.54/2.51  --sup_immed_bw_main                     []
% 15.54/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.54/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.54/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.54/2.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.54/2.51  
% 15.54/2.51  ------ Combination Options
% 15.54/2.51  
% 15.54/2.51  --comb_res_mult                         3
% 15.54/2.51  --comb_sup_mult                         2
% 15.54/2.51  --comb_inst_mult                        10
% 15.54/2.51  
% 15.54/2.51  ------ Debug Options
% 15.54/2.51  
% 15.54/2.51  --dbg_backtrace                         false
% 15.54/2.51  --dbg_dump_prop_clauses                 false
% 15.54/2.51  --dbg_dump_prop_clauses_file            -
% 15.54/2.51  --dbg_out_stat                          false
% 15.54/2.51  
% 15.54/2.51  
% 15.54/2.51  
% 15.54/2.51  
% 15.54/2.51  ------ Proving...
% 15.54/2.51  
% 15.54/2.51  
% 15.54/2.51  % SZS status Theorem for theBenchmark.p
% 15.54/2.51  
% 15.54/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 15.54/2.51  
% 15.54/2.51  fof(f2,axiom,(
% 15.54/2.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.54/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.54/2.51  
% 15.54/2.51  fof(f35,plain,(
% 15.54/2.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.54/2.51    inference(nnf_transformation,[],[f2])).
% 15.54/2.51  
% 15.54/2.51  fof(f51,plain,(
% 15.54/2.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.54/2.51    inference(cnf_transformation,[],[f35])).
% 15.54/2.51  
% 15.54/2.51  fof(f1,axiom,(
% 15.54/2.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.54/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.54/2.51  
% 15.54/2.51  fof(f33,plain,(
% 15.54/2.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.54/2.51    inference(nnf_transformation,[],[f1])).
% 15.54/2.51  
% 15.54/2.51  fof(f34,plain,(
% 15.54/2.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.54/2.51    inference(flattening,[],[f33])).
% 15.54/2.51  
% 15.54/2.51  fof(f50,plain,(
% 15.54/2.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.54/2.51    inference(cnf_transformation,[],[f34])).
% 15.54/2.51  
% 15.54/2.51  fof(f9,axiom,(
% 15.54/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.54/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.54/2.51  
% 15.54/2.51  fof(f25,plain,(
% 15.54/2.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.54/2.51    inference(ennf_transformation,[],[f9])).
% 15.54/2.51  
% 15.54/2.51  fof(f60,plain,(
% 15.54/2.51    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.54/2.51    inference(cnf_transformation,[],[f25])).
% 15.54/2.51  
% 15.54/2.51  fof(f12,axiom,(
% 15.54/2.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 15.54/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.54/2.51  
% 15.54/2.51  fof(f29,plain,(
% 15.54/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.54/2.51    inference(ennf_transformation,[],[f12])).
% 15.54/2.51  
% 15.54/2.51  fof(f30,plain,(
% 15.54/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.54/2.51    inference(flattening,[],[f29])).
% 15.54/2.51  
% 15.54/2.51  fof(f39,plain,(
% 15.54/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.54/2.51    inference(nnf_transformation,[],[f30])).
% 15.54/2.51  
% 15.54/2.51  fof(f64,plain,(
% 15.54/2.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.54/2.51    inference(cnf_transformation,[],[f39])).
% 15.54/2.51  
% 15.54/2.51  fof(f86,plain,(
% 15.54/2.51    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.54/2.51    inference(equality_resolution,[],[f64])).
% 15.54/2.51  
% 15.54/2.51  fof(f10,axiom,(
% 15.54/2.51    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 15.54/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.54/2.51  
% 15.54/2.51  fof(f26,plain,(
% 15.54/2.51    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 15.54/2.51    inference(ennf_transformation,[],[f10])).
% 15.54/2.51  
% 15.54/2.51  fof(f61,plain,(
% 15.54/2.51    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 15.54/2.51    inference(cnf_transformation,[],[f26])).
% 15.54/2.51  
% 15.54/2.51  fof(f13,conjecture,(
% 15.54/2.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 15.54/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.54/2.51  
% 15.54/2.51  fof(f14,negated_conjecture,(
% 15.54/2.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 15.54/2.51    inference(negated_conjecture,[],[f13])).
% 15.54/2.51  
% 15.54/2.51  fof(f31,plain,(
% 15.54/2.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 15.54/2.51    inference(ennf_transformation,[],[f14])).
% 15.54/2.51  
% 15.54/2.51  fof(f32,plain,(
% 15.54/2.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 15.54/2.51    inference(flattening,[],[f31])).
% 15.54/2.51  
% 15.54/2.51  fof(f46,plain,(
% 15.54/2.51    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) & sK7 = X5 & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 15.54/2.51    introduced(choice_axiom,[])).
% 15.54/2.51  
% 15.54/2.51  fof(f45,plain,(
% 15.54/2.51    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK6 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 15.54/2.51    introduced(choice_axiom,[])).
% 15.54/2.51  
% 15.54/2.51  fof(f44,plain,(
% 15.54/2.51    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK5,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 15.54/2.51    introduced(choice_axiom,[])).
% 15.54/2.51  
% 15.54/2.51  fof(f43,plain,(
% 15.54/2.51    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK4,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK4 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 15.54/2.51    introduced(choice_axiom,[])).
% 15.54/2.51  
% 15.54/2.51  fof(f42,plain,(
% 15.54/2.51    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 15.54/2.51    introduced(choice_axiom,[])).
% 15.54/2.51  
% 15.54/2.51  fof(f41,plain,(
% 15.54/2.51    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK2,X4,X5) & r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 15.54/2.51    introduced(choice_axiom,[])).
% 15.54/2.51  
% 15.54/2.51  fof(f40,plain,(
% 15.54/2.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 15.54/2.51    introduced(choice_axiom,[])).
% 15.54/2.51  
% 15.54/2.51  fof(f47,plain,(
% 15.54/2.51    ((((((~r1_tmap_1(sK4,sK2,sK5,sK6) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 15.54/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f32,f46,f45,f44,f43,f42,f41,f40])).
% 15.54/2.51  
% 15.54/2.51  fof(f78,plain,(
% 15.54/2.51    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f8,axiom,(
% 15.54/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 15.54/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.54/2.51  
% 15.54/2.51  fof(f15,plain,(
% 15.54/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 15.54/2.51    inference(pure_predicate_removal,[],[f8])).
% 15.54/2.51  
% 15.54/2.51  fof(f24,plain,(
% 15.54/2.51    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.54/2.51    inference(ennf_transformation,[],[f15])).
% 15.54/2.51  
% 15.54/2.51  fof(f59,plain,(
% 15.54/2.51    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.54/2.51    inference(cnf_transformation,[],[f24])).
% 15.54/2.51  
% 15.54/2.51  fof(f6,axiom,(
% 15.54/2.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.54/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.54/2.51  
% 15.54/2.51  fof(f20,plain,(
% 15.54/2.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.54/2.51    inference(ennf_transformation,[],[f6])).
% 15.54/2.51  
% 15.54/2.51  fof(f21,plain,(
% 15.54/2.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.54/2.51    inference(flattening,[],[f20])).
% 15.54/2.51  
% 15.54/2.51  fof(f57,plain,(
% 15.54/2.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.54/2.51    inference(cnf_transformation,[],[f21])).
% 15.54/2.51  
% 15.54/2.51  fof(f5,axiom,(
% 15.54/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 15.54/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.54/2.51  
% 15.54/2.51  fof(f19,plain,(
% 15.54/2.51    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 15.54/2.51    inference(ennf_transformation,[],[f5])).
% 15.54/2.51  
% 15.54/2.51  fof(f36,plain,(
% 15.54/2.51    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 15.54/2.51    inference(nnf_transformation,[],[f19])).
% 15.54/2.51  
% 15.54/2.51  fof(f55,plain,(
% 15.54/2.51    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 15.54/2.51    inference(cnf_transformation,[],[f36])).
% 15.54/2.51  
% 15.54/2.51  fof(f4,axiom,(
% 15.54/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 15.54/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.54/2.51  
% 15.54/2.51  fof(f18,plain,(
% 15.54/2.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.54/2.51    inference(ennf_transformation,[],[f4])).
% 15.54/2.51  
% 15.54/2.51  fof(f54,plain,(
% 15.54/2.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.54/2.51    inference(cnf_transformation,[],[f18])).
% 15.54/2.51  
% 15.54/2.51  fof(f67,plain,(
% 15.54/2.51    l1_pre_topc(sK1)),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f72,plain,(
% 15.54/2.51    m1_pre_topc(sK3,sK1)),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f3,axiom,(
% 15.54/2.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 15.54/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.54/2.51  
% 15.54/2.51  fof(f16,plain,(
% 15.54/2.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.54/2.51    inference(ennf_transformation,[],[f3])).
% 15.54/2.51  
% 15.54/2.51  fof(f17,plain,(
% 15.54/2.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.54/2.51    inference(flattening,[],[f16])).
% 15.54/2.51  
% 15.54/2.51  fof(f53,plain,(
% 15.54/2.51    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.54/2.51    inference(cnf_transformation,[],[f17])).
% 15.54/2.51  
% 15.54/2.51  fof(f7,axiom,(
% 15.54/2.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 15.54/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.54/2.51  
% 15.54/2.51  fof(f22,plain,(
% 15.54/2.51    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.54/2.51    inference(ennf_transformation,[],[f7])).
% 15.54/2.51  
% 15.54/2.51  fof(f23,plain,(
% 15.54/2.51    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.54/2.51    inference(flattening,[],[f22])).
% 15.54/2.51  
% 15.54/2.51  fof(f37,plain,(
% 15.54/2.51    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK0(X0,X1),X0,X1))),
% 15.54/2.51    introduced(choice_axiom,[])).
% 15.54/2.51  
% 15.54/2.51  fof(f38,plain,(
% 15.54/2.51    ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.54/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f37])).
% 15.54/2.51  
% 15.54/2.51  fof(f58,plain,(
% 15.54/2.51    ( ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.54/2.51    inference(cnf_transformation,[],[f38])).
% 15.54/2.51  
% 15.54/2.51  fof(f80,plain,(
% 15.54/2.51    m1_subset_1(sK7,u1_struct_0(sK3))),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f81,plain,(
% 15.54/2.51    sK6 = sK7),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f82,plain,(
% 15.54/2.51    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f83,plain,(
% 15.54/2.51    ~r1_tmap_1(sK4,sK2,sK5,sK6)),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f79,plain,(
% 15.54/2.51    m1_subset_1(sK6,u1_struct_0(sK4))),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f77,plain,(
% 15.54/2.51    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f76,plain,(
% 15.54/2.51    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f75,plain,(
% 15.54/2.51    v1_funct_1(sK5)),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f74,plain,(
% 15.54/2.51    m1_pre_topc(sK4,sK1)),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f73,plain,(
% 15.54/2.51    ~v2_struct_0(sK4)),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f71,plain,(
% 15.54/2.51    ~v2_struct_0(sK3)),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f70,plain,(
% 15.54/2.51    l1_pre_topc(sK2)),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f69,plain,(
% 15.54/2.51    v2_pre_topc(sK2)),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f68,plain,(
% 15.54/2.51    ~v2_struct_0(sK2)),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f66,plain,(
% 15.54/2.51    v2_pre_topc(sK1)),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  fof(f65,plain,(
% 15.54/2.51    ~v2_struct_0(sK1)),
% 15.54/2.51    inference(cnf_transformation,[],[f47])).
% 15.54/2.51  
% 15.54/2.51  cnf(c_591,plain,
% 15.54/2.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,X2) | X2 != X1 ),
% 15.54/2.51      theory(equality) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_7026,plain,
% 15.54/2.51      ( ~ r1_tarski(sK0(sK4,sK6),X0)
% 15.54/2.51      | r1_tarski(sK0(sK4,sK6),X1)
% 15.54/2.51      | X1 != X0 ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_591]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_17112,plain,
% 15.54/2.51      ( r1_tarski(sK0(sK4,sK6),X0)
% 15.54/2.51      | ~ r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4))
% 15.54/2.51      | X0 != u1_struct_0(sK4) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_7026]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_72367,plain,
% 15.54/2.51      ( r1_tarski(sK0(sK4,sK6),u1_struct_0(sK3))
% 15.54/2.51      | ~ r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4))
% 15.54/2.51      | u1_struct_0(sK3) != u1_struct_0(sK4) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_17112]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_4,plain,
% 15.54/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.54/2.51      inference(cnf_transformation,[],[f51]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_2914,plain,
% 15.54/2.51      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(X0))
% 15.54/2.51      | r1_tarski(u1_struct_0(sK4),X0) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_4]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_3969,plain,
% 15.54/2.51      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(X0)))
% 15.54/2.51      | r1_tarski(u1_struct_0(sK4),u1_struct_0(X0)) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_2914]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_32566,plain,
% 15.54/2.51      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 15.54/2.51      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_3969]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_0,plain,
% 15.54/2.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.54/2.51      inference(cnf_transformation,[],[f50]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_2423,plain,
% 15.54/2.51      ( ~ r1_tarski(X0,u1_struct_0(sK3))
% 15.54/2.51      | ~ r1_tarski(u1_struct_0(sK3),X0)
% 15.54/2.51      | u1_struct_0(sK3) = X0 ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_0]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_19870,plain,
% 15.54/2.51      ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
% 15.54/2.51      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK3))
% 15.54/2.51      | u1_struct_0(sK3) = u1_struct_0(sK4) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_2423]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_12,plain,
% 15.54/2.51      ( ~ m1_pre_topc(X0,X1)
% 15.54/2.51      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.54/2.51      | ~ l1_pre_topc(X1) ),
% 15.54/2.51      inference(cnf_transformation,[],[f60]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_3970,plain,
% 15.54/2.51      ( ~ m1_pre_topc(sK4,X0)
% 15.54/2.51      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(X0)))
% 15.54/2.51      | ~ l1_pre_topc(X0) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_12]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_15669,plain,
% 15.54/2.51      ( ~ m1_pre_topc(sK4,sK3)
% 15.54/2.51      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 15.54/2.51      | ~ l1_pre_topc(sK3) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_3970]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_2338,plain,
% 15.54/2.51      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0))
% 15.54/2.51      | r1_tarski(u1_struct_0(sK3),X0) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_4]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_3694,plain,
% 15.54/2.51      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
% 15.54/2.51      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0)) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_2338]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_10990,plain,
% 15.54/2.51      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 15.54/2.51      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_3694]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_7015,plain,
% 15.54/2.51      ( ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(X0))
% 15.54/2.51      | r1_tarski(sK0(sK4,sK6),X0) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_4]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_10946,plain,
% 15.54/2.51      ( ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 15.54/2.51      | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4)) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_7015]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_3695,plain,
% 15.54/2.51      ( ~ m1_pre_topc(sK3,X0)
% 15.54/2.51      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
% 15.54/2.51      | ~ l1_pre_topc(X0) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_12]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_8372,plain,
% 15.54/2.51      ( ~ m1_pre_topc(sK3,sK4)
% 15.54/2.51      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 15.54/2.51      | ~ l1_pre_topc(sK4) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_3695]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_15,plain,
% 15.54/2.51      ( r1_tmap_1(X0,X1,X2,X3)
% 15.54/2.51      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 15.54/2.51      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 15.54/2.51      | ~ m1_connsp_2(X6,X0,X3)
% 15.54/2.51      | ~ m1_pre_topc(X4,X5)
% 15.54/2.51      | ~ m1_pre_topc(X4,X0)
% 15.54/2.51      | ~ m1_pre_topc(X0,X5)
% 15.54/2.51      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 15.54/2.51      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.54/2.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.54/2.51      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 15.54/2.51      | ~ r1_tarski(X6,u1_struct_0(X4))
% 15.54/2.51      | ~ v1_funct_1(X2)
% 15.54/2.51      | v2_struct_0(X5)
% 15.54/2.51      | v2_struct_0(X1)
% 15.54/2.51      | v2_struct_0(X4)
% 15.54/2.51      | v2_struct_0(X0)
% 15.54/2.51      | ~ l1_pre_topc(X5)
% 15.54/2.51      | ~ l1_pre_topc(X1)
% 15.54/2.51      | ~ v2_pre_topc(X5)
% 15.54/2.51      | ~ v2_pre_topc(X1) ),
% 15.54/2.51      inference(cnf_transformation,[],[f86]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_3133,plain,
% 15.54/2.51      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,X3),sK6)
% 15.54/2.51      | r1_tmap_1(sK4,X1,X3,sK6)
% 15.54/2.51      | ~ v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(X1))
% 15.54/2.51      | ~ m1_connsp_2(sK0(sK4,sK6),sK4,sK6)
% 15.54/2.51      | ~ m1_pre_topc(X0,X2)
% 15.54/2.51      | ~ m1_pre_topc(X0,sK4)
% 15.54/2.51      | ~ m1_pre_topc(sK4,X2)
% 15.54/2.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 15.54/2.51      | ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 15.54/2.51      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 15.54/2.51      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 15.54/2.51      | ~ r1_tarski(sK0(sK4,sK6),u1_struct_0(X0))
% 15.54/2.51      | ~ v1_funct_1(X3)
% 15.54/2.51      | v2_struct_0(X1)
% 15.54/2.51      | v2_struct_0(X0)
% 15.54/2.51      | v2_struct_0(X2)
% 15.54/2.51      | v2_struct_0(sK4)
% 15.54/2.51      | ~ l1_pre_topc(X1)
% 15.54/2.51      | ~ l1_pre_topc(X2)
% 15.54/2.51      | ~ v2_pre_topc(X1)
% 15.54/2.51      | ~ v2_pre_topc(X2) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_15]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_4851,plain,
% 15.54/2.51      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),sK6)
% 15.54/2.51      | r1_tmap_1(sK4,X1,sK5,sK6)
% 15.54/2.51      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(X1))
% 15.54/2.51      | ~ m1_connsp_2(sK0(sK4,sK6),sK4,sK6)
% 15.54/2.51      | ~ m1_pre_topc(X0,X2)
% 15.54/2.51      | ~ m1_pre_topc(X0,sK4)
% 15.54/2.51      | ~ m1_pre_topc(sK4,X2)
% 15.54/2.51      | ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 15.54/2.51      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 15.54/2.51      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 15.54/2.51      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 15.54/2.51      | ~ r1_tarski(sK0(sK4,sK6),u1_struct_0(X0))
% 15.54/2.51      | ~ v1_funct_1(sK5)
% 15.54/2.51      | v2_struct_0(X0)
% 15.54/2.51      | v2_struct_0(X1)
% 15.54/2.51      | v2_struct_0(X2)
% 15.54/2.51      | v2_struct_0(sK4)
% 15.54/2.51      | ~ l1_pre_topc(X1)
% 15.54/2.51      | ~ l1_pre_topc(X2)
% 15.54/2.51      | ~ v2_pre_topc(X1)
% 15.54/2.51      | ~ v2_pre_topc(X2) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_3133]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_6813,plain,
% 15.54/2.51      ( ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)
% 15.54/2.51      | r1_tmap_1(sK4,sK2,sK5,sK6)
% 15.54/2.51      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
% 15.54/2.51      | ~ m1_connsp_2(sK0(sK4,sK6),sK4,sK6)
% 15.54/2.51      | ~ m1_pre_topc(sK3,sK1)
% 15.54/2.51      | ~ m1_pre_topc(sK3,sK4)
% 15.54/2.51      | ~ m1_pre_topc(sK4,sK1)
% 15.54/2.51      | ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 15.54/2.51      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 15.54/2.51      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 15.54/2.51      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 15.54/2.51      | ~ r1_tarski(sK0(sK4,sK6),u1_struct_0(sK3))
% 15.54/2.51      | ~ v1_funct_1(sK5)
% 15.54/2.51      | v2_struct_0(sK1)
% 15.54/2.51      | v2_struct_0(sK3)
% 15.54/2.51      | v2_struct_0(sK2)
% 15.54/2.51      | v2_struct_0(sK4)
% 15.54/2.51      | ~ l1_pre_topc(sK1)
% 15.54/2.51      | ~ l1_pre_topc(sK2)
% 15.54/2.51      | ~ v2_pre_topc(sK1)
% 15.54/2.51      | ~ v2_pre_topc(sK2) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_4851]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_13,plain,
% 15.54/2.51      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 15.54/2.51      inference(cnf_transformation,[],[f61]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_1422,plain,
% 15.54/2.51      ( m1_pre_topc(X0,X0) = iProver_top
% 15.54/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.54/2.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_22,negated_conjecture,
% 15.54/2.51      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
% 15.54/2.51      inference(cnf_transformation,[],[f78]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_11,plain,
% 15.54/2.51      ( ~ m1_pre_topc(X0,X1)
% 15.54/2.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 15.54/2.51      | ~ l1_pre_topc(X1) ),
% 15.54/2.51      inference(cnf_transformation,[],[f59]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_1424,plain,
% 15.54/2.51      ( m1_pre_topc(X0,X1) != iProver_top
% 15.54/2.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 15.54/2.51      | l1_pre_topc(X1) != iProver_top ),
% 15.54/2.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_3034,plain,
% 15.54/2.51      ( m1_pre_topc(sK3,X0) != iProver_top
% 15.54/2.51      | m1_pre_topc(sK4,X0) = iProver_top
% 15.54/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.54/2.51      inference(superposition,[status(thm)],[c_22,c_1424]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_3192,plain,
% 15.54/2.51      ( m1_pre_topc(sK4,sK3) = iProver_top
% 15.54/2.51      | l1_pre_topc(sK3) != iProver_top ),
% 15.54/2.51      inference(superposition,[status(thm)],[c_1422,c_3034]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_3209,plain,
% 15.54/2.51      ( m1_pre_topc(sK4,sK3) | ~ l1_pre_topc(sK3) ),
% 15.54/2.51      inference(predicate_to_equality_rev,[status(thm)],[c_3192]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_9,plain,
% 15.54/2.51      ( ~ m1_connsp_2(X0,X1,X2)
% 15.54/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.54/2.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.54/2.51      | v2_struct_0(X1)
% 15.54/2.51      | ~ l1_pre_topc(X1)
% 15.54/2.51      | ~ v2_pre_topc(X1) ),
% 15.54/2.51      inference(cnf_transformation,[],[f57]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_3124,plain,
% 15.54/2.51      ( ~ m1_connsp_2(sK0(sK4,sK6),sK4,sK6)
% 15.54/2.51      | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 15.54/2.51      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 15.54/2.51      | v2_struct_0(sK4)
% 15.54/2.51      | ~ l1_pre_topc(sK4)
% 15.54/2.51      | ~ v2_pre_topc(sK4) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_9]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_8,plain,
% 15.54/2.51      ( ~ m1_pre_topc(X0,X1)
% 15.54/2.51      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.54/2.51      | ~ l1_pre_topc(X0)
% 15.54/2.51      | ~ l1_pre_topc(X1) ),
% 15.54/2.51      inference(cnf_transformation,[],[f55]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_6,plain,
% 15.54/2.51      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 15.54/2.51      inference(cnf_transformation,[],[f54]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_326,plain,
% 15.54/2.51      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.54/2.51      | ~ m1_pre_topc(X0,X1)
% 15.54/2.51      | ~ l1_pre_topc(X1) ),
% 15.54/2.51      inference(global_propositional_subsumption,[status(thm)],[c_8,c_6]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_327,plain,
% 15.54/2.51      ( ~ m1_pre_topc(X0,X1)
% 15.54/2.51      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.54/2.51      | ~ l1_pre_topc(X1) ),
% 15.54/2.51      inference(renaming,[status(thm)],[c_326]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_1401,plain,
% 15.54/2.51      ( m1_pre_topc(X0,X1) != iProver_top
% 15.54/2.51      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 15.54/2.51      | l1_pre_topc(X1) != iProver_top ),
% 15.54/2.51      inference(predicate_to_equality,[status(thm)],[c_327]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_1756,plain,
% 15.54/2.51      ( m1_pre_topc(X0,sK3) != iProver_top
% 15.54/2.51      | m1_pre_topc(X0,sK4) = iProver_top
% 15.54/2.51      | l1_pre_topc(sK3) != iProver_top ),
% 15.54/2.51      inference(superposition,[status(thm)],[c_22,c_1401]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_33,negated_conjecture,
% 15.54/2.51      ( l1_pre_topc(sK1) ),
% 15.54/2.51      inference(cnf_transformation,[],[f67]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_38,plain,
% 15.54/2.51      ( l1_pre_topc(sK1) = iProver_top ),
% 15.54/2.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_28,negated_conjecture,
% 15.54/2.51      ( m1_pre_topc(sK3,sK1) ),
% 15.54/2.51      inference(cnf_transformation,[],[f72]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_43,plain,
% 15.54/2.51      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 15.54/2.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_1866,plain,
% 15.54/2.51      ( ~ m1_pre_topc(sK3,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK3) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_6]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_2013,plain,
% 15.54/2.51      ( ~ m1_pre_topc(sK3,sK1) | ~ l1_pre_topc(sK1) | l1_pre_topc(sK3) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_1866]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_2014,plain,
% 15.54/2.51      ( m1_pre_topc(sK3,sK1) != iProver_top
% 15.54/2.51      | l1_pre_topc(sK1) != iProver_top
% 15.54/2.51      | l1_pre_topc(sK3) = iProver_top ),
% 15.54/2.51      inference(predicate_to_equality,[status(thm)],[c_2013]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_3020,plain,
% 15.54/2.51      ( m1_pre_topc(X0,sK4) = iProver_top
% 15.54/2.51      | m1_pre_topc(X0,sK3) != iProver_top ),
% 15.54/2.51      inference(global_propositional_subsumption,
% 15.54/2.51                [status(thm)],
% 15.54/2.51                [c_1756,c_38,c_43,c_2014]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_3021,plain,
% 15.54/2.51      ( m1_pre_topc(X0,sK3) != iProver_top
% 15.54/2.51      | m1_pre_topc(X0,sK4) = iProver_top ),
% 15.54/2.51      inference(renaming,[status(thm)],[c_3020]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_3028,plain,
% 15.54/2.51      ( m1_pre_topc(sK3,sK4) = iProver_top
% 15.54/2.51      | l1_pre_topc(sK3) != iProver_top ),
% 15.54/2.51      inference(superposition,[status(thm)],[c_1422,c_3021]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_3029,plain,
% 15.54/2.51      ( m1_pre_topc(sK3,sK4) | ~ l1_pre_topc(sK3) ),
% 15.54/2.51      inference(predicate_to_equality_rev,[status(thm)],[c_3028]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_5,plain,
% 15.54/2.51      ( ~ m1_pre_topc(X0,X1)
% 15.54/2.51      | ~ l1_pre_topc(X1)
% 15.54/2.51      | ~ v2_pre_topc(X1)
% 15.54/2.51      | v2_pre_topc(X0) ),
% 15.54/2.51      inference(cnf_transformation,[],[f53]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_2123,plain,
% 15.54/2.51      ( ~ m1_pre_topc(sK4,X0)
% 15.54/2.51      | ~ l1_pre_topc(X0)
% 15.54/2.51      | ~ v2_pre_topc(X0)
% 15.54/2.51      | v2_pre_topc(sK4) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_5]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_2693,plain,
% 15.54/2.51      ( ~ m1_pre_topc(sK4,sK1)
% 15.54/2.51      | ~ l1_pre_topc(sK1)
% 15.54/2.51      | ~ v2_pre_topc(sK1)
% 15.54/2.51      | v2_pre_topc(sK4) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_2123]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_1876,plain,
% 15.54/2.51      ( ~ m1_pre_topc(sK4,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK4) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_6]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_2069,plain,
% 15.54/2.51      ( ~ m1_pre_topc(sK4,sK1) | ~ l1_pre_topc(sK1) | l1_pre_topc(sK4) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_1876]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_10,plain,
% 15.54/2.51      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 15.54/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.54/2.51      | v2_struct_0(X0)
% 15.54/2.51      | ~ l1_pre_topc(X0)
% 15.54/2.51      | ~ v2_pre_topc(X0) ),
% 15.54/2.51      inference(cnf_transformation,[],[f58]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_1829,plain,
% 15.54/2.51      ( m1_connsp_2(sK0(sK4,sK6),sK4,sK6)
% 15.54/2.51      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 15.54/2.51      | v2_struct_0(sK4)
% 15.54/2.51      | ~ l1_pre_topc(sK4)
% 15.54/2.51      | ~ v2_pre_topc(sK4) ),
% 15.54/2.51      inference(instantiation,[status(thm)],[c_10]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_20,negated_conjecture,
% 15.54/2.51      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 15.54/2.51      inference(cnf_transformation,[],[f80]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_1416,plain,
% 15.54/2.51      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 15.54/2.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_19,negated_conjecture,
% 15.54/2.51      ( sK6 = sK7 ),
% 15.54/2.51      inference(cnf_transformation,[],[f81]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_1462,plain,
% 15.54/2.51      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 15.54/2.51      inference(light_normalisation,[status(thm)],[c_1416,c_19]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_1679,plain,
% 15.54/2.51      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 15.54/2.51      inference(predicate_to_equality_rev,[status(thm)],[c_1462]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_18,negated_conjecture,
% 15.54/2.51      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
% 15.54/2.51      inference(cnf_transformation,[],[f82]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_1417,plain,
% 15.54/2.51      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
% 15.54/2.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_1477,plain,
% 15.54/2.51      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) = iProver_top ),
% 15.54/2.51      inference(light_normalisation,[status(thm)],[c_1417,c_19]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_1673,plain,
% 15.54/2.51      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) ),
% 15.54/2.51      inference(predicate_to_equality_rev,[status(thm)],[c_1477]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_17,negated_conjecture,
% 15.54/2.51      ( ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
% 15.54/2.51      inference(cnf_transformation,[],[f83]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_21,negated_conjecture,
% 15.54/2.51      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 15.54/2.51      inference(cnf_transformation,[],[f79]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_23,negated_conjecture,
% 15.54/2.51      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 15.54/2.51      inference(cnf_transformation,[],[f77]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_24,negated_conjecture,
% 15.54/2.51      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 15.54/2.51      inference(cnf_transformation,[],[f76]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_25,negated_conjecture,
% 15.54/2.51      ( v1_funct_1(sK5) ),
% 15.54/2.51      inference(cnf_transformation,[],[f75]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_26,negated_conjecture,
% 15.54/2.51      ( m1_pre_topc(sK4,sK1) ),
% 15.54/2.51      inference(cnf_transformation,[],[f74]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_27,negated_conjecture,
% 15.54/2.51      ( ~ v2_struct_0(sK4) ),
% 15.54/2.51      inference(cnf_transformation,[],[f73]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_29,negated_conjecture,
% 15.54/2.51      ( ~ v2_struct_0(sK3) ),
% 15.54/2.51      inference(cnf_transformation,[],[f71]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_30,negated_conjecture,
% 15.54/2.51      ( l1_pre_topc(sK2) ),
% 15.54/2.51      inference(cnf_transformation,[],[f70]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_31,negated_conjecture,
% 15.54/2.51      ( v2_pre_topc(sK2) ),
% 15.54/2.51      inference(cnf_transformation,[],[f69]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_32,negated_conjecture,
% 15.54/2.51      ( ~ v2_struct_0(sK2) ),
% 15.54/2.51      inference(cnf_transformation,[],[f68]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_34,negated_conjecture,
% 15.54/2.51      ( v2_pre_topc(sK1) ),
% 15.54/2.51      inference(cnf_transformation,[],[f66]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(c_35,negated_conjecture,
% 15.54/2.51      ( ~ v2_struct_0(sK1) ),
% 15.54/2.51      inference(cnf_transformation,[],[f65]) ).
% 15.54/2.51  
% 15.54/2.51  cnf(contradiction,plain,
% 15.54/2.51      ( $false ),
% 15.54/2.51      inference(minisat,
% 15.54/2.51                [status(thm)],
% 15.54/2.51                [c_72367,c_32566,c_19870,c_15669,c_10990,c_10946,c_8372,
% 15.54/2.51                 c_6813,c_3209,c_3124,c_3029,c_2693,c_2069,c_2013,c_1829,
% 15.54/2.51                 c_1679,c_1673,c_17,c_21,c_23,c_24,c_25,c_26,c_27,c_28,
% 15.54/2.51                 c_29,c_30,c_31,c_32,c_33,c_34,c_35]) ).
% 15.54/2.51  
% 15.54/2.51  
% 15.54/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 15.54/2.51  
% 15.54/2.51  ------                               Statistics
% 15.54/2.51  
% 15.54/2.51  ------ Selected
% 15.54/2.51  
% 15.54/2.51  total_time:                             1.928
% 15.54/2.51  
%------------------------------------------------------------------------------
