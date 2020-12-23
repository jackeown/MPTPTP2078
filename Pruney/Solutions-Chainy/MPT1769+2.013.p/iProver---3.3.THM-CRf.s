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
% DateTime   : Thu Dec  3 12:23:04 EST 2020

% Result     : Theorem 0.74s
% Output     : CNFRefutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  149 (1715 expanded)
%              Number of clauses        :   83 ( 261 expanded)
%              Number of leaves         :   17 ( 748 expanded)
%              Depth                    :   20
%              Number of atoms          :  906 (37865 expanded)
%              Number of equality atoms :  211 (2358 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X4 = X5
      | ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ! [X6] :
                              ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                             => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                  & X0 = X3 )
                               => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
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
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                    & X0 = X3 )
                                 => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                  <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f22])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(nnf_transformation,[],[f23])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
            | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
          & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
            | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
          & X0 = X3
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X6) )
     => ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK7),X5) )
        & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
          | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK7),X5) )
        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK7)
        & X0 = X3
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
              & X0 = X3
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X6) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ? [X6] :
            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK6)
              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK6) )
            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK6)
              | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK6) )
            & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
            & X0 = X3
            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X6) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                    | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                  & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                    | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                  & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                  & X0 = X3
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X6) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK5,X2),X5)
                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK5,X2),X5)
                  | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK5,X6)
                & X0 = X3
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X6) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                        | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                      & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                        | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                      & X0 = X3
                      & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X6) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X6),X5) )
                    & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X6),X5) )
                    & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK4),u1_struct_0(X1),X4,X6)
                    & sK4 = X0
                    & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                    & v1_funct_2(X6,u1_struct_0(sK4),u1_struct_0(X1))
                    & v1_funct_1(X6) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                            | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                          & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                            | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                          & X0 = X3
                          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X6) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK3),X5)
                          | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X6),X5) )
                        & ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK3),X5)
                          | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X6),X5) )
                        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                        & X0 = X3
                        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X6) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
                    & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X4,X2),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X6),X5) )
                            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X4,X2),X5)
                              | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X6),X5) )
                            & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X3),u1_struct_0(sK2),X4,X6)
                            & X0 = X3
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK2))
                            & v1_funct_1(X6) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK2))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK2))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                                & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                  | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                & X0 = X3
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK1,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK1,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(sK1),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & sK1 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X1))
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

fof(f40,plain,
    ( ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) )
    & ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6)
      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) )
    & r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)
    & sK1 = sK4
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f32,f39,f38,f37,f36,f35,f34,f33])).

fof(f74,plain,(
    r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,(
    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f73,plain,(
    sK1 = sK4 ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6)
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6)
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3327,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | X4 = X5 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_15,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_434,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | X3 = X0
    | u1_struct_0(sK4) != X4
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK2) != X5
    | u1_struct_0(sK2) != X2
    | sK7 != X3
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_435,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(u1_struct_0(sK2))
    | sK7 = sK5 ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_437,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | sK7 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_435,c_25,c_24,c_23,c_19,c_18,c_17])).

cnf(c_3297,plain,
    ( sK7 = sK5
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3323,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3316,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( sK1 = sK4 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3374,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3316,c_16])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3322,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4615,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3374,c_3322])).

cnf(c_4851,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3323,c_4615])).

cnf(c_5905,plain,
    ( sK7 = sK5
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3297,c_4851])).

cnf(c_6290,plain,
    ( sK7 = sK5
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3327,c_5905])).

cnf(c_3310,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4614,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3310,c_3322])).

cnf(c_4809,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3323,c_4614])).

cnf(c_4816,plain,
    ( sK7 = sK5
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3297,c_4809])).

cnf(c_6247,plain,
    ( sK7 = sK5
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3327,c_4816])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3325,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6475,plain,
    ( sK7 = sK5
    | sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6247,c_3325])).

cnf(c_6533,plain,
    ( sK7 = sK5 ),
    inference(superposition,[status(thm)],[c_6290,c_6475])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3307,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3354,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3307,c_16])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3305,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3320,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X4) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_pre_topc(X0,X4) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X4) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3319,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X0,X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3462,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_pre_topc(X0,X4) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X4) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X4) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3320,c_3319])).

cnf(c_5529,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
    | v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3374,c_3462])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_39,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_40,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_41,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_52,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3315,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3363,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3315,c_16])).

cnf(c_6202,plain,
    ( v2_pre_topc(X1) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5529,c_39,c_40,c_41,c_52,c_3363])).

cnf(c_6203,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6202])).

cnf(c_6214,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(sK3)) = k3_tmap_1(X0,sK2,sK1,sK3,sK7)
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3305,c_6203])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3321,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4714,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0)
    | v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3374,c_3321])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_36,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_37,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_38,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5008,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4714,c_36,c_37,c_38,c_39,c_40,c_41,c_52,c_3363])).

cnf(c_5009,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0)
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5008])).

cnf(c_5016,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(sK3)) = k2_tmap_1(sK1,sK2,sK7,sK3) ),
    inference(superposition,[status(thm)],[c_3305,c_5009])).

cnf(c_6232,plain,
    ( k3_tmap_1(X0,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3)
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6214,c_5016])).

cnf(c_6660,plain,
    ( k3_tmap_1(sK1,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3)
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3354,c_6232])).

cnf(c_6663,plain,
    ( k3_tmap_1(sK1,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6660,c_36,c_37,c_38])).

cnf(c_14,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3317,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3407,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3317,c_16])).

cnf(c_6666,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK7,sK3),sK6) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6663,c_3407])).

cnf(c_6752,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6533,c_6666])).

cnf(c_13,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3318,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3412,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3318,c_16])).

cnf(c_6667,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK7,sK3),sK6) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6663,c_3412])).

cnf(c_6753,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6533,c_6667])).

cnf(c_6770,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6752,c_6753])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n025.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 10:19:20 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 0.74/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.74/1.04  
% 0.74/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.74/1.04  
% 0.74/1.04  ------  iProver source info
% 0.74/1.04  
% 0.74/1.04  git: date: 2020-06-30 10:37:57 +0100
% 0.74/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.74/1.04  git: non_committed_changes: false
% 0.74/1.04  git: last_make_outside_of_git: false
% 0.74/1.04  
% 0.74/1.04  ------ 
% 0.74/1.04  
% 0.74/1.04  ------ Input Options
% 0.74/1.04  
% 0.74/1.04  --out_options                           all
% 0.74/1.04  --tptp_safe_out                         true
% 0.74/1.04  --problem_path                          ""
% 0.74/1.04  --include_path                          ""
% 0.74/1.04  --clausifier                            res/vclausify_rel
% 0.74/1.04  --clausifier_options                    --mode clausify
% 0.74/1.04  --stdin                                 false
% 0.74/1.04  --stats_out                             all
% 0.74/1.04  
% 0.74/1.04  ------ General Options
% 0.74/1.04  
% 0.74/1.04  --fof                                   false
% 0.74/1.04  --time_out_real                         305.
% 0.74/1.04  --time_out_virtual                      -1.
% 0.74/1.04  --symbol_type_check                     false
% 0.74/1.04  --clausify_out                          false
% 0.74/1.04  --sig_cnt_out                           false
% 0.74/1.04  --trig_cnt_out                          false
% 0.74/1.04  --trig_cnt_out_tolerance                1.
% 0.74/1.04  --trig_cnt_out_sk_spl                   false
% 0.74/1.04  --abstr_cl_out                          false
% 0.74/1.04  
% 0.74/1.04  ------ Global Options
% 0.74/1.04  
% 0.74/1.04  --schedule                              default
% 0.74/1.04  --add_important_lit                     false
% 0.74/1.04  --prop_solver_per_cl                    1000
% 0.74/1.04  --min_unsat_core                        false
% 0.74/1.04  --soft_assumptions                      false
% 0.74/1.04  --soft_lemma_size                       3
% 0.74/1.04  --prop_impl_unit_size                   0
% 0.74/1.04  --prop_impl_unit                        []
% 0.74/1.04  --share_sel_clauses                     true
% 0.74/1.04  --reset_solvers                         false
% 0.74/1.04  --bc_imp_inh                            [conj_cone]
% 0.74/1.04  --conj_cone_tolerance                   3.
% 0.74/1.04  --extra_neg_conj                        none
% 0.74/1.04  --large_theory_mode                     true
% 0.74/1.04  --prolific_symb_bound                   200
% 0.74/1.04  --lt_threshold                          2000
% 0.74/1.04  --clause_weak_htbl                      true
% 0.74/1.04  --gc_record_bc_elim                     false
% 0.74/1.04  
% 0.74/1.04  ------ Preprocessing Options
% 0.74/1.04  
% 0.74/1.04  --preprocessing_flag                    true
% 0.74/1.04  --time_out_prep_mult                    0.1
% 0.74/1.04  --splitting_mode                        input
% 0.74/1.04  --splitting_grd                         true
% 0.74/1.04  --splitting_cvd                         false
% 0.74/1.04  --splitting_cvd_svl                     false
% 0.74/1.04  --splitting_nvd                         32
% 0.74/1.04  --sub_typing                            true
% 0.74/1.04  --prep_gs_sim                           true
% 0.74/1.04  --prep_unflatten                        true
% 0.74/1.04  --prep_res_sim                          true
% 0.74/1.04  --prep_upred                            true
% 0.74/1.04  --prep_sem_filter                       exhaustive
% 0.74/1.04  --prep_sem_filter_out                   false
% 0.74/1.04  --pred_elim                             true
% 0.74/1.04  --res_sim_input                         true
% 0.74/1.04  --eq_ax_congr_red                       true
% 0.74/1.04  --pure_diseq_elim                       true
% 0.74/1.04  --brand_transform                       false
% 0.74/1.04  --non_eq_to_eq                          false
% 0.74/1.04  --prep_def_merge                        true
% 0.74/1.04  --prep_def_merge_prop_impl              false
% 0.74/1.04  --prep_def_merge_mbd                    true
% 0.74/1.04  --prep_def_merge_tr_red                 false
% 0.74/1.04  --prep_def_merge_tr_cl                  false
% 0.74/1.04  --smt_preprocessing                     true
% 0.74/1.04  --smt_ac_axioms                         fast
% 0.74/1.04  --preprocessed_out                      false
% 0.74/1.04  --preprocessed_stats                    false
% 0.74/1.04  
% 0.74/1.04  ------ Abstraction refinement Options
% 0.74/1.04  
% 0.74/1.04  --abstr_ref                             []
% 0.74/1.04  --abstr_ref_prep                        false
% 0.74/1.04  --abstr_ref_until_sat                   false
% 0.74/1.04  --abstr_ref_sig_restrict                funpre
% 0.74/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.74/1.04  --abstr_ref_under                       []
% 0.74/1.04  
% 0.74/1.04  ------ SAT Options
% 0.74/1.04  
% 0.74/1.04  --sat_mode                              false
% 0.74/1.04  --sat_fm_restart_options                ""
% 0.74/1.04  --sat_gr_def                            false
% 0.74/1.04  --sat_epr_types                         true
% 0.74/1.04  --sat_non_cyclic_types                  false
% 0.74/1.04  --sat_finite_models                     false
% 0.74/1.04  --sat_fm_lemmas                         false
% 0.74/1.04  --sat_fm_prep                           false
% 0.74/1.04  --sat_fm_uc_incr                        true
% 0.74/1.04  --sat_out_model                         small
% 0.74/1.04  --sat_out_clauses                       false
% 0.74/1.04  
% 0.74/1.04  ------ QBF Options
% 0.74/1.04  
% 0.74/1.04  --qbf_mode                              false
% 0.74/1.04  --qbf_elim_univ                         false
% 0.74/1.04  --qbf_dom_inst                          none
% 0.74/1.04  --qbf_dom_pre_inst                      false
% 0.74/1.04  --qbf_sk_in                             false
% 0.74/1.04  --qbf_pred_elim                         true
% 0.74/1.04  --qbf_split                             512
% 0.74/1.04  
% 0.74/1.04  ------ BMC1 Options
% 0.74/1.04  
% 0.74/1.04  --bmc1_incremental                      false
% 0.74/1.04  --bmc1_axioms                           reachable_all
% 0.74/1.04  --bmc1_min_bound                        0
% 0.74/1.04  --bmc1_max_bound                        -1
% 0.74/1.04  --bmc1_max_bound_default                -1
% 0.74/1.04  --bmc1_symbol_reachability              true
% 0.74/1.04  --bmc1_property_lemmas                  false
% 0.74/1.04  --bmc1_k_induction                      false
% 0.74/1.04  --bmc1_non_equiv_states                 false
% 0.74/1.04  --bmc1_deadlock                         false
% 0.74/1.04  --bmc1_ucm                              false
% 0.74/1.04  --bmc1_add_unsat_core                   none
% 0.74/1.04  --bmc1_unsat_core_children              false
% 0.74/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.74/1.04  --bmc1_out_stat                         full
% 0.74/1.04  --bmc1_ground_init                      false
% 0.74/1.04  --bmc1_pre_inst_next_state              false
% 0.74/1.04  --bmc1_pre_inst_state                   false
% 0.74/1.04  --bmc1_pre_inst_reach_state             false
% 0.74/1.04  --bmc1_out_unsat_core                   false
% 0.74/1.04  --bmc1_aig_witness_out                  false
% 0.74/1.04  --bmc1_verbose                          false
% 0.74/1.04  --bmc1_dump_clauses_tptp                false
% 0.74/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.74/1.04  --bmc1_dump_file                        -
% 0.74/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.74/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.74/1.04  --bmc1_ucm_extend_mode                  1
% 0.74/1.04  --bmc1_ucm_init_mode                    2
% 0.74/1.04  --bmc1_ucm_cone_mode                    none
% 0.74/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.74/1.04  --bmc1_ucm_relax_model                  4
% 0.74/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.74/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.74/1.04  --bmc1_ucm_layered_model                none
% 0.74/1.04  --bmc1_ucm_max_lemma_size               10
% 0.74/1.04  
% 0.74/1.04  ------ AIG Options
% 0.74/1.04  
% 0.74/1.04  --aig_mode                              false
% 0.74/1.04  
% 0.74/1.04  ------ Instantiation Options
% 0.74/1.04  
% 0.74/1.04  --instantiation_flag                    true
% 0.74/1.04  --inst_sos_flag                         false
% 0.74/1.04  --inst_sos_phase                        true
% 0.74/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.74/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.74/1.04  --inst_lit_sel_side                     num_symb
% 0.74/1.04  --inst_solver_per_active                1400
% 0.74/1.04  --inst_solver_calls_frac                1.
% 0.74/1.04  --inst_passive_queue_type               priority_queues
% 0.74/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.74/1.04  --inst_passive_queues_freq              [25;2]
% 0.74/1.04  --inst_dismatching                      true
% 0.74/1.04  --inst_eager_unprocessed_to_passive     true
% 0.74/1.04  --inst_prop_sim_given                   true
% 0.74/1.04  --inst_prop_sim_new                     false
% 0.74/1.04  --inst_subs_new                         false
% 0.74/1.04  --inst_eq_res_simp                      false
% 0.74/1.04  --inst_subs_given                       false
% 0.74/1.04  --inst_orphan_elimination               true
% 0.74/1.04  --inst_learning_loop_flag               true
% 0.74/1.04  --inst_learning_start                   3000
% 0.74/1.04  --inst_learning_factor                  2
% 0.74/1.04  --inst_start_prop_sim_after_learn       3
% 0.74/1.04  --inst_sel_renew                        solver
% 0.74/1.04  --inst_lit_activity_flag                true
% 0.74/1.04  --inst_restr_to_given                   false
% 0.74/1.04  --inst_activity_threshold               500
% 0.74/1.04  --inst_out_proof                        true
% 0.74/1.04  
% 0.74/1.04  ------ Resolution Options
% 0.74/1.04  
% 0.74/1.04  --resolution_flag                       true
% 0.74/1.04  --res_lit_sel                           adaptive
% 0.74/1.04  --res_lit_sel_side                      none
% 0.74/1.04  --res_ordering                          kbo
% 0.74/1.04  --res_to_prop_solver                    active
% 0.74/1.04  --res_prop_simpl_new                    false
% 0.74/1.04  --res_prop_simpl_given                  true
% 0.74/1.04  --res_passive_queue_type                priority_queues
% 0.74/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.74/1.04  --res_passive_queues_freq               [15;5]
% 0.74/1.04  --res_forward_subs                      full
% 0.74/1.04  --res_backward_subs                     full
% 0.74/1.04  --res_forward_subs_resolution           true
% 0.74/1.04  --res_backward_subs_resolution          true
% 0.74/1.04  --res_orphan_elimination                true
% 0.74/1.04  --res_time_limit                        2.
% 0.74/1.04  --res_out_proof                         true
% 0.74/1.04  
% 0.74/1.04  ------ Superposition Options
% 0.74/1.04  
% 0.74/1.04  --superposition_flag                    true
% 0.74/1.04  --sup_passive_queue_type                priority_queues
% 0.74/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.74/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.74/1.04  --demod_completeness_check              fast
% 0.74/1.04  --demod_use_ground                      true
% 0.74/1.04  --sup_to_prop_solver                    passive
% 0.74/1.04  --sup_prop_simpl_new                    true
% 0.74/1.04  --sup_prop_simpl_given                  true
% 0.74/1.04  --sup_fun_splitting                     false
% 0.74/1.04  --sup_smt_interval                      50000
% 0.74/1.04  
% 0.74/1.04  ------ Superposition Simplification Setup
% 0.74/1.04  
% 0.74/1.04  --sup_indices_passive                   []
% 0.74/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.74/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.74/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.74/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.74/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.74/1.04  --sup_full_bw                           [BwDemod]
% 0.74/1.04  --sup_immed_triv                        [TrivRules]
% 0.74/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.74/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.74/1.04  --sup_immed_bw_main                     []
% 0.74/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.74/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.74/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.74/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.74/1.04  
% 0.74/1.04  ------ Combination Options
% 0.74/1.04  
% 0.74/1.04  --comb_res_mult                         3
% 0.74/1.04  --comb_sup_mult                         2
% 0.74/1.04  --comb_inst_mult                        10
% 0.74/1.04  
% 0.74/1.04  ------ Debug Options
% 0.74/1.04  
% 0.74/1.04  --dbg_backtrace                         false
% 0.74/1.04  --dbg_dump_prop_clauses                 false
% 0.74/1.04  --dbg_dump_prop_clauses_file            -
% 0.74/1.04  --dbg_out_stat                          false
% 0.74/1.04  ------ Parsing...
% 0.74/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.74/1.04  
% 0.74/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 0.74/1.04  
% 0.74/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.74/1.04  
% 0.74/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.74/1.04  ------ Proving...
% 0.74/1.04  ------ Problem Properties 
% 0.74/1.04  
% 0.74/1.04  
% 0.74/1.04  clauses                                 33
% 0.74/1.04  conjectures                             22
% 0.74/1.04  EPR                                     18
% 0.74/1.04  Horn                                    28
% 0.74/1.04  unary                                   21
% 0.74/1.04  binary                                  6
% 0.74/1.04  lits                                    71
% 0.74/1.04  lits eq                                 5
% 0.74/1.04  fd_pure                                 0
% 0.74/1.04  fd_pseudo                               0
% 0.74/1.04  fd_cond                                 0
% 0.74/1.04  fd_pseudo_cond                          1
% 0.74/1.04  AC symbols                              0
% 0.74/1.04  
% 0.74/1.04  ------ Schedule dynamic 5 is on 
% 0.74/1.04  
% 0.74/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.74/1.04  
% 0.74/1.04  
% 0.74/1.04  ------ 
% 0.74/1.04  Current options:
% 0.74/1.04  ------ 
% 0.74/1.04  
% 0.74/1.04  ------ Input Options
% 0.74/1.04  
% 0.74/1.04  --out_options                           all
% 0.74/1.04  --tptp_safe_out                         true
% 0.74/1.04  --problem_path                          ""
% 0.74/1.04  --include_path                          ""
% 0.74/1.04  --clausifier                            res/vclausify_rel
% 0.74/1.04  --clausifier_options                    --mode clausify
% 0.74/1.04  --stdin                                 false
% 0.74/1.04  --stats_out                             all
% 0.74/1.04  
% 0.74/1.04  ------ General Options
% 0.74/1.04  
% 0.74/1.04  --fof                                   false
% 0.74/1.04  --time_out_real                         305.
% 0.74/1.04  --time_out_virtual                      -1.
% 0.74/1.04  --symbol_type_check                     false
% 0.74/1.04  --clausify_out                          false
% 0.74/1.04  --sig_cnt_out                           false
% 0.74/1.04  --trig_cnt_out                          false
% 0.74/1.04  --trig_cnt_out_tolerance                1.
% 0.74/1.04  --trig_cnt_out_sk_spl                   false
% 0.74/1.04  --abstr_cl_out                          false
% 0.74/1.04  
% 0.74/1.04  ------ Global Options
% 0.74/1.04  
% 0.74/1.04  --schedule                              default
% 0.74/1.04  --add_important_lit                     false
% 0.74/1.04  --prop_solver_per_cl                    1000
% 0.74/1.04  --min_unsat_core                        false
% 0.74/1.04  --soft_assumptions                      false
% 0.74/1.04  --soft_lemma_size                       3
% 0.74/1.04  --prop_impl_unit_size                   0
% 0.74/1.04  --prop_impl_unit                        []
% 0.74/1.04  --share_sel_clauses                     true
% 0.74/1.04  --reset_solvers                         false
% 0.74/1.04  --bc_imp_inh                            [conj_cone]
% 0.74/1.04  --conj_cone_tolerance                   3.
% 0.74/1.04  --extra_neg_conj                        none
% 0.74/1.04  --large_theory_mode                     true
% 0.74/1.04  --prolific_symb_bound                   200
% 0.74/1.04  --lt_threshold                          2000
% 0.74/1.04  --clause_weak_htbl                      true
% 0.74/1.04  --gc_record_bc_elim                     false
% 0.74/1.04  
% 0.74/1.04  ------ Preprocessing Options
% 0.74/1.04  
% 0.74/1.04  --preprocessing_flag                    true
% 0.74/1.04  --time_out_prep_mult                    0.1
% 0.74/1.04  --splitting_mode                        input
% 0.74/1.04  --splitting_grd                         true
% 0.74/1.04  --splitting_cvd                         false
% 0.74/1.04  --splitting_cvd_svl                     false
% 0.74/1.04  --splitting_nvd                         32
% 0.74/1.04  --sub_typing                            true
% 0.74/1.04  --prep_gs_sim                           true
% 0.74/1.04  --prep_unflatten                        true
% 0.74/1.04  --prep_res_sim                          true
% 0.74/1.04  --prep_upred                            true
% 0.74/1.04  --prep_sem_filter                       exhaustive
% 0.74/1.04  --prep_sem_filter_out                   false
% 0.74/1.04  --pred_elim                             true
% 0.74/1.04  --res_sim_input                         true
% 0.74/1.04  --eq_ax_congr_red                       true
% 0.74/1.04  --pure_diseq_elim                       true
% 0.74/1.04  --brand_transform                       false
% 0.74/1.04  --non_eq_to_eq                          false
% 0.74/1.04  --prep_def_merge                        true
% 0.74/1.04  --prep_def_merge_prop_impl              false
% 0.74/1.04  --prep_def_merge_mbd                    true
% 0.74/1.04  --prep_def_merge_tr_red                 false
% 0.74/1.04  --prep_def_merge_tr_cl                  false
% 0.74/1.04  --smt_preprocessing                     true
% 0.74/1.04  --smt_ac_axioms                         fast
% 0.74/1.04  --preprocessed_out                      false
% 0.74/1.04  --preprocessed_stats                    false
% 0.74/1.04  
% 0.74/1.04  ------ Abstraction refinement Options
% 0.74/1.04  
% 0.74/1.04  --abstr_ref                             []
% 0.74/1.04  --abstr_ref_prep                        false
% 0.74/1.04  --abstr_ref_until_sat                   false
% 0.74/1.04  --abstr_ref_sig_restrict                funpre
% 0.74/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.74/1.04  --abstr_ref_under                       []
% 0.74/1.04  
% 0.74/1.04  ------ SAT Options
% 0.74/1.04  
% 0.74/1.04  --sat_mode                              false
% 0.74/1.04  --sat_fm_restart_options                ""
% 0.74/1.04  --sat_gr_def                            false
% 0.74/1.04  --sat_epr_types                         true
% 0.74/1.04  --sat_non_cyclic_types                  false
% 0.74/1.04  --sat_finite_models                     false
% 0.74/1.04  --sat_fm_lemmas                         false
% 0.74/1.04  --sat_fm_prep                           false
% 0.74/1.04  --sat_fm_uc_incr                        true
% 0.74/1.04  --sat_out_model                         small
% 0.74/1.04  --sat_out_clauses                       false
% 0.74/1.04  
% 0.74/1.04  ------ QBF Options
% 0.74/1.04  
% 0.74/1.04  --qbf_mode                              false
% 0.74/1.04  --qbf_elim_univ                         false
% 0.74/1.04  --qbf_dom_inst                          none
% 0.74/1.04  --qbf_dom_pre_inst                      false
% 0.74/1.04  --qbf_sk_in                             false
% 0.74/1.04  --qbf_pred_elim                         true
% 0.74/1.04  --qbf_split                             512
% 0.74/1.04  
% 0.74/1.04  ------ BMC1 Options
% 0.74/1.04  
% 0.74/1.04  --bmc1_incremental                      false
% 0.74/1.04  --bmc1_axioms                           reachable_all
% 0.74/1.04  --bmc1_min_bound                        0
% 0.74/1.04  --bmc1_max_bound                        -1
% 0.74/1.04  --bmc1_max_bound_default                -1
% 0.74/1.04  --bmc1_symbol_reachability              true
% 0.74/1.04  --bmc1_property_lemmas                  false
% 0.74/1.04  --bmc1_k_induction                      false
% 0.74/1.04  --bmc1_non_equiv_states                 false
% 0.74/1.04  --bmc1_deadlock                         false
% 0.74/1.04  --bmc1_ucm                              false
% 0.74/1.04  --bmc1_add_unsat_core                   none
% 0.74/1.04  --bmc1_unsat_core_children              false
% 0.74/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.74/1.04  --bmc1_out_stat                         full
% 0.74/1.04  --bmc1_ground_init                      false
% 0.74/1.04  --bmc1_pre_inst_next_state              false
% 0.74/1.04  --bmc1_pre_inst_state                   false
% 0.74/1.04  --bmc1_pre_inst_reach_state             false
% 0.74/1.04  --bmc1_out_unsat_core                   false
% 0.74/1.04  --bmc1_aig_witness_out                  false
% 0.74/1.04  --bmc1_verbose                          false
% 0.74/1.04  --bmc1_dump_clauses_tptp                false
% 0.74/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.74/1.04  --bmc1_dump_file                        -
% 0.74/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.74/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.74/1.04  --bmc1_ucm_extend_mode                  1
% 0.74/1.04  --bmc1_ucm_init_mode                    2
% 0.74/1.04  --bmc1_ucm_cone_mode                    none
% 0.74/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.74/1.04  --bmc1_ucm_relax_model                  4
% 0.74/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.74/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.74/1.04  --bmc1_ucm_layered_model                none
% 0.74/1.04  --bmc1_ucm_max_lemma_size               10
% 0.74/1.04  
% 0.74/1.04  ------ AIG Options
% 0.74/1.04  
% 0.74/1.04  --aig_mode                              false
% 0.74/1.04  
% 0.74/1.04  ------ Instantiation Options
% 0.74/1.04  
% 0.74/1.04  --instantiation_flag                    true
% 0.74/1.04  --inst_sos_flag                         false
% 0.74/1.04  --inst_sos_phase                        true
% 0.74/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.74/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.74/1.04  --inst_lit_sel_side                     none
% 0.74/1.04  --inst_solver_per_active                1400
% 0.74/1.04  --inst_solver_calls_frac                1.
% 0.74/1.04  --inst_passive_queue_type               priority_queues
% 0.74/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.74/1.04  --inst_passive_queues_freq              [25;2]
% 0.74/1.04  --inst_dismatching                      true
% 0.74/1.04  --inst_eager_unprocessed_to_passive     true
% 0.74/1.04  --inst_prop_sim_given                   true
% 0.74/1.04  --inst_prop_sim_new                     false
% 0.74/1.04  --inst_subs_new                         false
% 0.74/1.04  --inst_eq_res_simp                      false
% 0.74/1.04  --inst_subs_given                       false
% 0.74/1.04  --inst_orphan_elimination               true
% 0.74/1.04  --inst_learning_loop_flag               true
% 0.74/1.04  --inst_learning_start                   3000
% 0.74/1.04  --inst_learning_factor                  2
% 0.74/1.04  --inst_start_prop_sim_after_learn       3
% 0.74/1.04  --inst_sel_renew                        solver
% 0.74/1.04  --inst_lit_activity_flag                true
% 0.74/1.04  --inst_restr_to_given                   false
% 0.74/1.04  --inst_activity_threshold               500
% 0.74/1.04  --inst_out_proof                        true
% 0.74/1.04  
% 0.74/1.04  ------ Resolution Options
% 0.74/1.04  
% 0.74/1.04  --resolution_flag                       false
% 0.74/1.04  --res_lit_sel                           adaptive
% 0.74/1.04  --res_lit_sel_side                      none
% 0.74/1.04  --res_ordering                          kbo
% 0.74/1.04  --res_to_prop_solver                    active
% 0.74/1.04  --res_prop_simpl_new                    false
% 0.74/1.04  --res_prop_simpl_given                  true
% 0.74/1.04  --res_passive_queue_type                priority_queues
% 0.74/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.74/1.04  --res_passive_queues_freq               [15;5]
% 0.74/1.04  --res_forward_subs                      full
% 0.74/1.04  --res_backward_subs                     full
% 0.74/1.04  --res_forward_subs_resolution           true
% 0.74/1.04  --res_backward_subs_resolution          true
% 0.74/1.04  --res_orphan_elimination                true
% 0.74/1.04  --res_time_limit                        2.
% 0.74/1.04  --res_out_proof                         true
% 0.74/1.04  
% 0.74/1.04  ------ Superposition Options
% 0.74/1.04  
% 0.74/1.04  --superposition_flag                    true
% 0.74/1.04  --sup_passive_queue_type                priority_queues
% 0.74/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.74/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.74/1.04  --demod_completeness_check              fast
% 0.74/1.04  --demod_use_ground                      true
% 0.74/1.04  --sup_to_prop_solver                    passive
% 0.74/1.04  --sup_prop_simpl_new                    true
% 0.74/1.04  --sup_prop_simpl_given                  true
% 0.74/1.04  --sup_fun_splitting                     false
% 0.74/1.04  --sup_smt_interval                      50000
% 0.74/1.04  
% 0.74/1.04  ------ Superposition Simplification Setup
% 0.74/1.04  
% 0.74/1.04  --sup_indices_passive                   []
% 0.74/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.74/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.74/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.74/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.74/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.74/1.04  --sup_full_bw                           [BwDemod]
% 0.74/1.04  --sup_immed_triv                        [TrivRules]
% 0.74/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.74/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.74/1.04  --sup_immed_bw_main                     []
% 0.74/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.74/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.74/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.74/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.74/1.04  
% 0.74/1.04  ------ Combination Options
% 0.74/1.04  
% 0.74/1.04  --comb_res_mult                         3
% 0.74/1.04  --comb_sup_mult                         2
% 0.74/1.04  --comb_inst_mult                        10
% 0.74/1.04  
% 0.74/1.04  ------ Debug Options
% 0.74/1.04  
% 0.74/1.04  --dbg_backtrace                         false
% 0.74/1.04  --dbg_dump_prop_clauses                 false
% 0.74/1.04  --dbg_dump_prop_clauses_file            -
% 0.74/1.04  --dbg_out_stat                          false
% 0.74/1.04  
% 0.74/1.04  
% 0.74/1.04  
% 0.74/1.04  
% 0.74/1.04  ------ Proving...
% 0.74/1.04  
% 0.74/1.04  
% 0.74/1.04  % SZS status Theorem for theBenchmark.p
% 0.74/1.04  
% 0.74/1.04   Resolution empty clause
% 0.74/1.04  
% 0.74/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.74/1.04  
% 0.74/1.04  fof(f1,axiom,(
% 0.74/1.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.74/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.04  
% 0.74/1.04  fof(f11,plain,(
% 0.74/1.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.74/1.04    inference(ennf_transformation,[],[f1])).
% 0.74/1.04  
% 0.74/1.04  fof(f24,plain,(
% 0.74/1.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.74/1.04    inference(nnf_transformation,[],[f11])).
% 0.74/1.04  
% 0.74/1.04  fof(f25,plain,(
% 0.74/1.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.74/1.04    inference(rectify,[],[f24])).
% 0.74/1.04  
% 0.74/1.04  fof(f26,plain,(
% 0.74/1.04    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 0.74/1.04    introduced(choice_axiom,[])).
% 0.74/1.04  
% 0.74/1.04  fof(f27,plain,(
% 0.74/1.04    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.74/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 0.74/1.04  
% 0.74/1.04  fof(f42,plain,(
% 0.74/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 0.74/1.04    inference(cnf_transformation,[],[f27])).
% 0.74/1.04  
% 0.74/1.04  fof(f5,axiom,(
% 0.74/1.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 0.74/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.04  
% 0.74/1.04  fof(f14,plain,(
% 0.74/1.04    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 0.74/1.04    inference(ennf_transformation,[],[f5])).
% 0.74/1.04  
% 0.74/1.04  fof(f15,plain,(
% 0.74/1.04    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.74/1.04    inference(flattening,[],[f14])).
% 0.74/1.04  
% 0.74/1.04  fof(f30,plain,(
% 0.74/1.04    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.74/1.04    inference(nnf_transformation,[],[f15])).
% 0.74/1.04  
% 0.74/1.04  fof(f49,plain,(
% 0.74/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 0.74/1.04    inference(cnf_transformation,[],[f30])).
% 0.74/1.04  
% 0.74/1.04  fof(f9,conjecture,(
% 0.74/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 0.74/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.04  
% 0.74/1.04  fof(f10,negated_conjecture,(
% 0.74/1.04    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 0.74/1.04    inference(negated_conjecture,[],[f9])).
% 0.74/1.04  
% 0.74/1.04  fof(f22,plain,(
% 0.74/1.04    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.74/1.04    inference(ennf_transformation,[],[f10])).
% 0.74/1.04  
% 0.74/1.04  fof(f23,plain,(
% 0.74/1.04    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.74/1.04    inference(flattening,[],[f22])).
% 0.74/1.04  
% 0.74/1.04  fof(f31,plain,(
% 0.74/1.04    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.74/1.04    inference(nnf_transformation,[],[f23])).
% 0.74/1.04  
% 0.74/1.04  fof(f32,plain,(
% 0.74/1.04    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.74/1.04    inference(flattening,[],[f31])).
% 0.74/1.04  
% 0.74/1.04  fof(f39,plain,(
% 0.74/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK7),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK7),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK7) & X0 = X3 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 0.74/1.04    introduced(choice_axiom,[])).
% 0.74/1.04  
% 0.74/1.04  fof(f38,plain,(
% 0.74/1.04    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK6) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK6)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK6) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK6)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 0.74/1.04    introduced(choice_axiom,[])).
% 0.74/1.04  
% 0.74/1.04  fof(f37,plain,(
% 0.74/1.04    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK5,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK5,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK5,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 0.74/1.04    introduced(choice_axiom,[])).
% 0.74/1.04  
% 0.74/1.04  fof(f36,plain,(
% 0.74/1.04    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK4),u1_struct_0(X1),X4,X6) & sK4 = X0 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 0.74/1.04    introduced(choice_axiom,[])).
% 0.74/1.04  
% 0.74/1.04  fof(f35,plain,(
% 0.74/1.04    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK3),X5) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X6),X5)) & (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK3),X5) | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 0.74/1.04    introduced(choice_axiom,[])).
% 0.74/1.04  
% 0.74/1.04  fof(f34,plain,(
% 0.74/1.04    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X3),u1_struct_0(sK2),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 0.74/1.04    introduced(choice_axiom,[])).
% 0.74/1.04  
% 0.74/1.04  fof(f33,plain,(
% 0.74/1.04    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK1,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK1,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK1),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK1 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.74/1.04    introduced(choice_axiom,[])).
% 0.74/1.04  
% 0.74/1.04  fof(f40,plain,(
% 0.74/1.04    (((((((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)) & (r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)) & r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) & sK1 = sK4 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.74/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f32,f39,f38,f37,f36,f35,f34,f33])).
% 0.74/1.04  
% 0.74/1.04  fof(f74,plain,(
% 0.74/1.04    r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  fof(f64,plain,(
% 0.74/1.04    v1_funct_1(sK5)),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  fof(f65,plain,(
% 0.74/1.04    v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  fof(f66,plain,(
% 0.74/1.04    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  fof(f70,plain,(
% 0.74/1.04    v1_funct_1(sK7)),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  fof(f71,plain,(
% 0.74/1.04    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2))),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  fof(f72,plain,(
% 0.74/1.04    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  fof(f3,axiom,(
% 0.74/1.04    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.74/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.04  
% 0.74/1.04  fof(f12,plain,(
% 0.74/1.04    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.74/1.04    inference(ennf_transformation,[],[f3])).
% 0.74/1.04  
% 0.74/1.04  fof(f47,plain,(
% 0.74/1.04    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 0.74/1.04    inference(cnf_transformation,[],[f12])).
% 0.74/1.04  
% 0.74/1.04  fof(f73,plain,(
% 0.74/1.04    sK1 = sK4),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  fof(f4,axiom,(
% 0.74/1.04    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.74/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.04  
% 0.74/1.04  fof(f13,plain,(
% 0.74/1.04    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.74/1.04    inference(ennf_transformation,[],[f4])).
% 0.74/1.04  
% 0.74/1.04  fof(f48,plain,(
% 0.74/1.04    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.74/1.04    inference(cnf_transformation,[],[f13])).
% 0.74/1.04  
% 0.74/1.04  fof(f2,axiom,(
% 0.74/1.04    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.74/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.04  
% 0.74/1.04  fof(f28,plain,(
% 0.74/1.04    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.74/1.04    inference(nnf_transformation,[],[f2])).
% 0.74/1.04  
% 0.74/1.04  fof(f29,plain,(
% 0.74/1.04    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.74/1.04    inference(flattening,[],[f28])).
% 0.74/1.04  
% 0.74/1.04  fof(f46,plain,(
% 0.74/1.04    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.74/1.04    inference(cnf_transformation,[],[f29])).
% 0.74/1.04  
% 0.74/1.04  fof(f63,plain,(
% 0.74/1.04    m1_pre_topc(sK4,sK1)),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  fof(f61,plain,(
% 0.74/1.04    m1_pre_topc(sK3,sK1)),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  fof(f7,axiom,(
% 0.74/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 0.74/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.04  
% 0.74/1.04  fof(f18,plain,(
% 0.74/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.74/1.04    inference(ennf_transformation,[],[f7])).
% 0.74/1.04  
% 0.74/1.04  fof(f19,plain,(
% 0.74/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.74/1.04    inference(flattening,[],[f18])).
% 0.74/1.04  
% 0.74/1.04  fof(f52,plain,(
% 0.74/1.04    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.74/1.04    inference(cnf_transformation,[],[f19])).
% 0.74/1.04  
% 0.74/1.04  fof(f8,axiom,(
% 0.74/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.74/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.04  
% 0.74/1.04  fof(f20,plain,(
% 0.74/1.04    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.74/1.04    inference(ennf_transformation,[],[f8])).
% 0.74/1.04  
% 0.74/1.04  fof(f21,plain,(
% 0.74/1.04    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.74/1.04    inference(flattening,[],[f20])).
% 0.74/1.04  
% 0.74/1.04  fof(f53,plain,(
% 0.74/1.04    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.74/1.04    inference(cnf_transformation,[],[f21])).
% 0.74/1.04  
% 0.74/1.04  fof(f57,plain,(
% 0.74/1.04    ~v2_struct_0(sK2)),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  fof(f58,plain,(
% 0.74/1.04    v2_pre_topc(sK2)),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  fof(f59,plain,(
% 0.74/1.04    l1_pre_topc(sK2)),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  fof(f6,axiom,(
% 0.74/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.74/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.04  
% 0.74/1.04  fof(f16,plain,(
% 0.74/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.74/1.04    inference(ennf_transformation,[],[f6])).
% 0.74/1.04  
% 0.74/1.04  fof(f17,plain,(
% 0.74/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.74/1.04    inference(flattening,[],[f16])).
% 0.74/1.04  
% 0.74/1.04  fof(f51,plain,(
% 0.74/1.04    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.74/1.04    inference(cnf_transformation,[],[f17])).
% 0.74/1.04  
% 0.74/1.04  fof(f54,plain,(
% 0.74/1.04    ~v2_struct_0(sK1)),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  fof(f55,plain,(
% 0.74/1.04    v2_pre_topc(sK1)),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  fof(f56,plain,(
% 0.74/1.04    l1_pre_topc(sK1)),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  fof(f75,plain,(
% 0.74/1.04    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  fof(f76,plain,(
% 0.74/1.04    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)),
% 0.74/1.04    inference(cnf_transformation,[],[f40])).
% 0.74/1.04  
% 0.74/1.04  cnf(c_1,plain,
% 0.74/1.04      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 0.74/1.04      inference(cnf_transformation,[],[f42]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3327,plain,
% 0.74/1.04      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 0.74/1.04      | r1_tarski(X0,X1) = iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_9,plain,
% 0.74/1.04      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 0.74/1.04      | ~ v1_funct_2(X5,X2,X3)
% 0.74/1.04      | ~ v1_funct_2(X4,X0,X1)
% 0.74/1.04      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 0.74/1.04      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.74/1.04      | ~ v1_funct_1(X5)
% 0.74/1.04      | ~ v1_funct_1(X4)
% 0.74/1.04      | v1_xboole_0(X1)
% 0.74/1.04      | v1_xboole_0(X3)
% 0.74/1.04      | X4 = X5 ),
% 0.74/1.04      inference(cnf_transformation,[],[f49]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_15,negated_conjecture,
% 0.74/1.04      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) ),
% 0.74/1.04      inference(cnf_transformation,[],[f74]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_434,plain,
% 0.74/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 0.74/1.04      | ~ v1_funct_2(X3,X4,X5)
% 0.74/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.74/1.04      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 0.74/1.04      | ~ v1_funct_1(X0)
% 0.74/1.04      | ~ v1_funct_1(X3)
% 0.74/1.04      | v1_xboole_0(X2)
% 0.74/1.04      | v1_xboole_0(X5)
% 0.74/1.04      | X3 = X0
% 0.74/1.04      | u1_struct_0(sK4) != X4
% 0.74/1.04      | u1_struct_0(sK1) != X1
% 0.74/1.04      | u1_struct_0(sK2) != X5
% 0.74/1.04      | u1_struct_0(sK2) != X2
% 0.74/1.04      | sK7 != X3
% 0.74/1.04      | sK5 != X0 ),
% 0.74/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_435,plain,
% 0.74/1.04      ( ~ v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2))
% 0.74/1.04      | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
% 0.74/1.04      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 0.74/1.04      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 0.74/1.04      | ~ v1_funct_1(sK7)
% 0.74/1.04      | ~ v1_funct_1(sK5)
% 0.74/1.04      | v1_xboole_0(u1_struct_0(sK2))
% 0.74/1.04      | sK7 = sK5 ),
% 0.74/1.04      inference(unflattening,[status(thm)],[c_434]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_25,negated_conjecture,
% 0.74/1.04      ( v1_funct_1(sK5) ),
% 0.74/1.04      inference(cnf_transformation,[],[f64]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_24,negated_conjecture,
% 0.74/1.04      ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 0.74/1.04      inference(cnf_transformation,[],[f65]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_23,negated_conjecture,
% 0.74/1.04      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 0.74/1.04      inference(cnf_transformation,[],[f66]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_19,negated_conjecture,
% 0.74/1.04      ( v1_funct_1(sK7) ),
% 0.74/1.04      inference(cnf_transformation,[],[f70]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_18,negated_conjecture,
% 0.74/1.04      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 0.74/1.04      inference(cnf_transformation,[],[f71]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_17,negated_conjecture,
% 0.74/1.04      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 0.74/1.04      inference(cnf_transformation,[],[f72]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_437,plain,
% 0.74/1.04      ( v1_xboole_0(u1_struct_0(sK2)) | sK7 = sK5 ),
% 0.74/1.04      inference(global_propositional_subsumption,
% 0.74/1.04                [status(thm)],
% 0.74/1.04                [c_435,c_25,c_24,c_23,c_19,c_18,c_17]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3297,plain,
% 0.74/1.04      ( sK7 = sK5 | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_6,plain,
% 0.74/1.04      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 0.74/1.04      inference(cnf_transformation,[],[f47]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3323,plain,
% 0.74/1.04      ( v1_xboole_0(X0) != iProver_top
% 0.74/1.04      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3316,plain,
% 0.74/1.04      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_16,negated_conjecture,
% 0.74/1.04      ( sK1 = sK4 ),
% 0.74/1.04      inference(cnf_transformation,[],[f73]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3374,plain,
% 0.74/1.04      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 0.74/1.04      inference(light_normalisation,[status(thm)],[c_3316,c_16]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_7,plain,
% 0.74/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.74/1.04      | ~ r2_hidden(X2,X0)
% 0.74/1.04      | ~ v1_xboole_0(X1) ),
% 0.74/1.04      inference(cnf_transformation,[],[f48]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3322,plain,
% 0.74/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 0.74/1.04      | r2_hidden(X2,X0) != iProver_top
% 0.74/1.04      | v1_xboole_0(X1) != iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_4615,plain,
% 0.74/1.04      ( r2_hidden(X0,sK7) != iProver_top
% 0.74/1.04      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top ),
% 0.74/1.04      inference(superposition,[status(thm)],[c_3374,c_3322]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_4851,plain,
% 0.74/1.04      ( r2_hidden(X0,sK7) != iProver_top
% 0.74/1.04      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 0.74/1.04      inference(superposition,[status(thm)],[c_3323,c_4615]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_5905,plain,
% 0.74/1.04      ( sK7 = sK5 | r2_hidden(X0,sK7) != iProver_top ),
% 0.74/1.04      inference(superposition,[status(thm)],[c_3297,c_4851]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_6290,plain,
% 0.74/1.04      ( sK7 = sK5 | r1_tarski(sK7,X0) = iProver_top ),
% 0.74/1.04      inference(superposition,[status(thm)],[c_3327,c_5905]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3310,plain,
% 0.74/1.04      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_4614,plain,
% 0.74/1.04      ( r2_hidden(X0,sK5) != iProver_top
% 0.74/1.04      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top ),
% 0.74/1.04      inference(superposition,[status(thm)],[c_3310,c_3322]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_4809,plain,
% 0.74/1.04      ( r2_hidden(X0,sK5) != iProver_top
% 0.74/1.04      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 0.74/1.04      inference(superposition,[status(thm)],[c_3323,c_4614]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_4816,plain,
% 0.74/1.04      ( sK7 = sK5 | r2_hidden(X0,sK5) != iProver_top ),
% 0.74/1.04      inference(superposition,[status(thm)],[c_3297,c_4809]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_6247,plain,
% 0.74/1.04      ( sK7 = sK5 | r1_tarski(sK5,X0) = iProver_top ),
% 0.74/1.04      inference(superposition,[status(thm)],[c_3327,c_4816]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3,plain,
% 0.74/1.04      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 0.74/1.04      inference(cnf_transformation,[],[f46]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3325,plain,
% 0.74/1.04      ( X0 = X1
% 0.74/1.04      | r1_tarski(X1,X0) != iProver_top
% 0.74/1.04      | r1_tarski(X0,X1) != iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_6475,plain,
% 0.74/1.04      ( sK7 = sK5 | sK5 = X0 | r1_tarski(X0,sK5) != iProver_top ),
% 0.74/1.04      inference(superposition,[status(thm)],[c_6247,c_3325]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_6533,plain,
% 0.74/1.04      ( sK7 = sK5 ),
% 0.74/1.04      inference(superposition,[status(thm)],[c_6290,c_6475]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_26,negated_conjecture,
% 0.74/1.04      ( m1_pre_topc(sK4,sK1) ),
% 0.74/1.04      inference(cnf_transformation,[],[f63]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3307,plain,
% 0.74/1.04      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3354,plain,
% 0.74/1.04      ( m1_pre_topc(sK1,sK1) = iProver_top ),
% 0.74/1.04      inference(light_normalisation,[status(thm)],[c_3307,c_16]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_28,negated_conjecture,
% 0.74/1.04      ( m1_pre_topc(sK3,sK1) ),
% 0.74/1.04      inference(cnf_transformation,[],[f61]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3305,plain,
% 0.74/1.04      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_11,plain,
% 0.74/1.04      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 0.74/1.04      | ~ m1_pre_topc(X3,X4)
% 0.74/1.04      | ~ m1_pre_topc(X3,X1)
% 0.74/1.04      | ~ m1_pre_topc(X1,X4)
% 0.74/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 0.74/1.04      | v2_struct_0(X4)
% 0.74/1.04      | v2_struct_0(X2)
% 0.74/1.04      | ~ v2_pre_topc(X2)
% 0.74/1.04      | ~ v2_pre_topc(X4)
% 0.74/1.04      | ~ l1_pre_topc(X2)
% 0.74/1.04      | ~ l1_pre_topc(X4)
% 0.74/1.04      | ~ v1_funct_1(X0)
% 0.74/1.04      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 0.74/1.04      inference(cnf_transformation,[],[f52]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3320,plain,
% 0.74/1.04      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
% 0.74/1.04      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 0.74/1.04      | m1_pre_topc(X3,X4) != iProver_top
% 0.74/1.04      | m1_pre_topc(X3,X0) != iProver_top
% 0.74/1.04      | m1_pre_topc(X0,X4) != iProver_top
% 0.74/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 0.74/1.04      | v2_struct_0(X4) = iProver_top
% 0.74/1.04      | v2_struct_0(X1) = iProver_top
% 0.74/1.04      | v2_pre_topc(X1) != iProver_top
% 0.74/1.04      | v2_pre_topc(X4) != iProver_top
% 0.74/1.04      | l1_pre_topc(X1) != iProver_top
% 0.74/1.04      | l1_pre_topc(X4) != iProver_top
% 0.74/1.04      | v1_funct_1(X2) != iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_12,plain,
% 0.74/1.04      ( ~ m1_pre_topc(X0,X1)
% 0.74/1.04      | ~ m1_pre_topc(X1,X2)
% 0.74/1.04      | m1_pre_topc(X0,X2)
% 0.74/1.04      | ~ v2_pre_topc(X2)
% 0.74/1.04      | ~ l1_pre_topc(X2) ),
% 0.74/1.04      inference(cnf_transformation,[],[f53]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3319,plain,
% 0.74/1.04      ( m1_pre_topc(X0,X1) != iProver_top
% 0.74/1.04      | m1_pre_topc(X1,X2) != iProver_top
% 0.74/1.04      | m1_pre_topc(X0,X2) = iProver_top
% 0.74/1.04      | v2_pre_topc(X2) != iProver_top
% 0.74/1.04      | l1_pre_topc(X2) != iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3462,plain,
% 0.74/1.04      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
% 0.74/1.04      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 0.74/1.04      | m1_pre_topc(X3,X0) != iProver_top
% 0.74/1.04      | m1_pre_topc(X0,X4) != iProver_top
% 0.74/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 0.74/1.04      | v2_struct_0(X4) = iProver_top
% 0.74/1.04      | v2_struct_0(X1) = iProver_top
% 0.74/1.04      | v2_pre_topc(X4) != iProver_top
% 0.74/1.04      | v2_pre_topc(X1) != iProver_top
% 0.74/1.04      | l1_pre_topc(X4) != iProver_top
% 0.74/1.04      | l1_pre_topc(X1) != iProver_top
% 0.74/1.04      | v1_funct_1(X2) != iProver_top ),
% 0.74/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_3320,c_3319]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_5529,plain,
% 0.74/1.04      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
% 0.74/1.04      | v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 0.74/1.04      | m1_pre_topc(X0,sK1) != iProver_top
% 0.74/1.04      | m1_pre_topc(sK1,X1) != iProver_top
% 0.74/1.04      | v2_struct_0(X1) = iProver_top
% 0.74/1.04      | v2_struct_0(sK2) = iProver_top
% 0.74/1.04      | v2_pre_topc(X1) != iProver_top
% 0.74/1.04      | v2_pre_topc(sK2) != iProver_top
% 0.74/1.04      | l1_pre_topc(X1) != iProver_top
% 0.74/1.04      | l1_pre_topc(sK2) != iProver_top
% 0.74/1.04      | v1_funct_1(sK7) != iProver_top ),
% 0.74/1.04      inference(superposition,[status(thm)],[c_3374,c_3462]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_32,negated_conjecture,
% 0.74/1.04      ( ~ v2_struct_0(sK2) ),
% 0.74/1.04      inference(cnf_transformation,[],[f57]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_39,plain,
% 0.74/1.04      ( v2_struct_0(sK2) != iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_31,negated_conjecture,
% 0.74/1.04      ( v2_pre_topc(sK2) ),
% 0.74/1.04      inference(cnf_transformation,[],[f58]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_40,plain,
% 0.74/1.04      ( v2_pre_topc(sK2) = iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_30,negated_conjecture,
% 0.74/1.04      ( l1_pre_topc(sK2) ),
% 0.74/1.04      inference(cnf_transformation,[],[f59]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_41,plain,
% 0.74/1.04      ( l1_pre_topc(sK2) = iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_52,plain,
% 0.74/1.04      ( v1_funct_1(sK7) = iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3315,plain,
% 0.74/1.04      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3363,plain,
% 0.74/1.04      ( v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 0.74/1.04      inference(light_normalisation,[status(thm)],[c_3315,c_16]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_6202,plain,
% 0.74/1.04      ( v2_pre_topc(X1) != iProver_top
% 0.74/1.04      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
% 0.74/1.04      | m1_pre_topc(X0,sK1) != iProver_top
% 0.74/1.04      | m1_pre_topc(sK1,X1) != iProver_top
% 0.74/1.04      | v2_struct_0(X1) = iProver_top
% 0.74/1.04      | l1_pre_topc(X1) != iProver_top ),
% 0.74/1.04      inference(global_propositional_subsumption,
% 0.74/1.04                [status(thm)],
% 0.74/1.04                [c_5529,c_39,c_40,c_41,c_52,c_3363]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_6203,plain,
% 0.74/1.04      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
% 0.74/1.04      | m1_pre_topc(X0,sK1) != iProver_top
% 0.74/1.04      | m1_pre_topc(sK1,X1) != iProver_top
% 0.74/1.04      | v2_struct_0(X1) = iProver_top
% 0.74/1.04      | v2_pre_topc(X1) != iProver_top
% 0.74/1.04      | l1_pre_topc(X1) != iProver_top ),
% 0.74/1.04      inference(renaming,[status(thm)],[c_6202]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_6214,plain,
% 0.74/1.04      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(sK3)) = k3_tmap_1(X0,sK2,sK1,sK3,sK7)
% 0.74/1.04      | m1_pre_topc(sK1,X0) != iProver_top
% 0.74/1.04      | v2_struct_0(X0) = iProver_top
% 0.74/1.04      | v2_pre_topc(X0) != iProver_top
% 0.74/1.04      | l1_pre_topc(X0) != iProver_top ),
% 0.74/1.04      inference(superposition,[status(thm)],[c_3305,c_6203]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_10,plain,
% 0.74/1.04      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 0.74/1.04      | ~ m1_pre_topc(X3,X1)
% 0.74/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 0.74/1.04      | v2_struct_0(X1)
% 0.74/1.04      | v2_struct_0(X2)
% 0.74/1.04      | ~ v2_pre_topc(X2)
% 0.74/1.04      | ~ v2_pre_topc(X1)
% 0.74/1.04      | ~ l1_pre_topc(X2)
% 0.74/1.04      | ~ l1_pre_topc(X1)
% 0.74/1.04      | ~ v1_funct_1(X0)
% 0.74/1.04      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 0.74/1.04      inference(cnf_transformation,[],[f51]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3321,plain,
% 0.74/1.04      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
% 0.74/1.04      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 0.74/1.04      | m1_pre_topc(X3,X0) != iProver_top
% 0.74/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 0.74/1.04      | v2_struct_0(X1) = iProver_top
% 0.74/1.04      | v2_struct_0(X0) = iProver_top
% 0.74/1.04      | v2_pre_topc(X1) != iProver_top
% 0.74/1.04      | v2_pre_topc(X0) != iProver_top
% 0.74/1.04      | l1_pre_topc(X1) != iProver_top
% 0.74/1.04      | l1_pre_topc(X0) != iProver_top
% 0.74/1.04      | v1_funct_1(X2) != iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_4714,plain,
% 0.74/1.04      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0)
% 0.74/1.04      | v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 0.74/1.04      | m1_pre_topc(X0,sK1) != iProver_top
% 0.74/1.04      | v2_struct_0(sK1) = iProver_top
% 0.74/1.04      | v2_struct_0(sK2) = iProver_top
% 0.74/1.04      | v2_pre_topc(sK1) != iProver_top
% 0.74/1.04      | v2_pre_topc(sK2) != iProver_top
% 0.74/1.04      | l1_pre_topc(sK1) != iProver_top
% 0.74/1.04      | l1_pre_topc(sK2) != iProver_top
% 0.74/1.04      | v1_funct_1(sK7) != iProver_top ),
% 0.74/1.04      inference(superposition,[status(thm)],[c_3374,c_3321]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_35,negated_conjecture,
% 0.74/1.04      ( ~ v2_struct_0(sK1) ),
% 0.74/1.04      inference(cnf_transformation,[],[f54]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_36,plain,
% 0.74/1.04      ( v2_struct_0(sK1) != iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_34,negated_conjecture,
% 0.74/1.04      ( v2_pre_topc(sK1) ),
% 0.74/1.04      inference(cnf_transformation,[],[f55]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_37,plain,
% 0.74/1.04      ( v2_pre_topc(sK1) = iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_33,negated_conjecture,
% 0.74/1.04      ( l1_pre_topc(sK1) ),
% 0.74/1.04      inference(cnf_transformation,[],[f56]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_38,plain,
% 0.74/1.04      ( l1_pre_topc(sK1) = iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_5008,plain,
% 0.74/1.04      ( m1_pre_topc(X0,sK1) != iProver_top
% 0.74/1.04      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0) ),
% 0.74/1.04      inference(global_propositional_subsumption,
% 0.74/1.04                [status(thm)],
% 0.74/1.04                [c_4714,c_36,c_37,c_38,c_39,c_40,c_41,c_52,c_3363]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_5009,plain,
% 0.74/1.04      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0)
% 0.74/1.04      | m1_pre_topc(X0,sK1) != iProver_top ),
% 0.74/1.04      inference(renaming,[status(thm)],[c_5008]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_5016,plain,
% 0.74/1.04      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(sK3)) = k2_tmap_1(sK1,sK2,sK7,sK3) ),
% 0.74/1.04      inference(superposition,[status(thm)],[c_3305,c_5009]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_6232,plain,
% 0.74/1.04      ( k3_tmap_1(X0,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3)
% 0.74/1.04      | m1_pre_topc(sK1,X0) != iProver_top
% 0.74/1.04      | v2_struct_0(X0) = iProver_top
% 0.74/1.04      | v2_pre_topc(X0) != iProver_top
% 0.74/1.04      | l1_pre_topc(X0) != iProver_top ),
% 0.74/1.04      inference(light_normalisation,[status(thm)],[c_6214,c_5016]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_6660,plain,
% 0.74/1.04      ( k3_tmap_1(sK1,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3)
% 0.74/1.04      | v2_struct_0(sK1) = iProver_top
% 0.74/1.04      | v2_pre_topc(sK1) != iProver_top
% 0.74/1.04      | l1_pre_topc(sK1) != iProver_top ),
% 0.74/1.04      inference(superposition,[status(thm)],[c_3354,c_6232]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_6663,plain,
% 0.74/1.04      ( k3_tmap_1(sK1,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3) ),
% 0.74/1.04      inference(global_propositional_subsumption,
% 0.74/1.04                [status(thm)],
% 0.74/1.04                [c_6660,c_36,c_37,c_38]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_14,negated_conjecture,
% 0.74/1.04      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
% 0.74/1.04      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
% 0.74/1.04      inference(cnf_transformation,[],[f75]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3317,plain,
% 0.74/1.04      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) = iProver_top
% 0.74/1.04      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3407,plain,
% 0.74/1.04      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) = iProver_top
% 0.74/1.04      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 0.74/1.04      inference(light_normalisation,[status(thm)],[c_3317,c_16]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_6666,plain,
% 0.74/1.04      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK7,sK3),sK6) = iProver_top
% 0.74/1.04      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 0.74/1.04      inference(demodulation,[status(thm)],[c_6663,c_3407]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_6752,plain,
% 0.74/1.04      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 0.74/1.04      inference(demodulation,[status(thm)],[c_6533,c_6666]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_13,negated_conjecture,
% 0.74/1.04      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
% 0.74/1.04      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
% 0.74/1.04      inference(cnf_transformation,[],[f76]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3318,plain,
% 0.74/1.04      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) != iProver_top
% 0.74/1.04      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 0.74/1.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_3412,plain,
% 0.74/1.04      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) != iProver_top
% 0.74/1.04      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 0.74/1.04      inference(light_normalisation,[status(thm)],[c_3318,c_16]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_6667,plain,
% 0.74/1.04      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK7,sK3),sK6) != iProver_top
% 0.74/1.04      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 0.74/1.04      inference(demodulation,[status(thm)],[c_6663,c_3412]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_6753,plain,
% 0.74/1.04      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 0.74/1.04      inference(demodulation,[status(thm)],[c_6533,c_6667]) ).
% 0.74/1.04  
% 0.74/1.04  cnf(c_6770,plain,
% 0.74/1.04      ( $false ),
% 0.74/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_6752,c_6753]) ).
% 0.74/1.04  
% 0.74/1.04  
% 0.74/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.74/1.04  
% 0.74/1.04  ------                               Statistics
% 0.74/1.04  
% 0.74/1.04  ------ General
% 0.74/1.04  
% 0.74/1.04  abstr_ref_over_cycles:                  0
% 0.74/1.04  abstr_ref_under_cycles:                 0
% 0.74/1.04  gc_basic_clause_elim:                   0
% 0.74/1.04  forced_gc_time:                         0
% 0.74/1.04  parsing_time:                           0.009
% 0.74/1.04  unif_index_cands_time:                  0.
% 0.74/1.04  unif_index_add_time:                    0.
% 0.74/1.04  orderings_time:                         0.
% 0.74/1.04  out_proof_time:                         0.01
% 0.74/1.04  total_time:                             0.224
% 0.74/1.04  num_of_symbols:                         57
% 0.74/1.04  num_of_terms:                           4417
% 0.74/1.04  
% 0.74/1.04  ------ Preprocessing
% 0.74/1.04  
% 0.74/1.04  num_of_splits:                          0
% 0.74/1.04  num_of_split_atoms:                     0
% 0.74/1.04  num_of_reused_defs:                     0
% 0.74/1.04  num_eq_ax_congr_red:                    18
% 0.74/1.04  num_of_sem_filtered_clauses:            1
% 0.74/1.04  num_of_subtypes:                        0
% 0.74/1.04  monotx_restored_types:                  0
% 0.74/1.04  sat_num_of_epr_types:                   0
% 0.74/1.04  sat_num_of_non_cyclic_types:            0
% 0.74/1.04  sat_guarded_non_collapsed_types:        0
% 0.74/1.04  num_pure_diseq_elim:                    0
% 0.74/1.04  simp_replaced_by:                       0
% 0.74/1.04  res_preprocessed:                       171
% 0.74/1.04  prep_upred:                             0
% 0.74/1.04  prep_unflattend:                        54
% 0.74/1.04  smt_new_axioms:                         0
% 0.74/1.04  pred_elim_cands:                        11
% 0.74/1.04  pred_elim:                              1
% 0.74/1.04  pred_elim_cl:                           2
% 0.74/1.04  pred_elim_cycles:                       7
% 0.74/1.04  merged_defs:                            8
% 0.74/1.04  merged_defs_ncl:                        0
% 0.74/1.04  bin_hyper_res:                          8
% 0.74/1.04  prep_cycles:                            4
% 0.74/1.04  pred_elim_time:                         0.057
% 0.74/1.04  splitting_time:                         0.
% 0.74/1.04  sem_filter_time:                        0.
% 0.74/1.04  monotx_time:                            0.
% 0.74/1.04  subtype_inf_time:                       0.
% 0.74/1.04  
% 0.74/1.04  ------ Problem properties
% 0.74/1.04  
% 0.74/1.04  clauses:                                33
% 0.74/1.04  conjectures:                            22
% 0.74/1.04  epr:                                    18
% 0.74/1.04  horn:                                   28
% 0.74/1.04  ground:                                 23
% 0.74/1.04  unary:                                  21
% 0.74/1.04  binary:                                 6
% 0.74/1.04  lits:                                   71
% 0.74/1.04  lits_eq:                                5
% 0.74/1.04  fd_pure:                                0
% 0.74/1.04  fd_pseudo:                              0
% 0.74/1.04  fd_cond:                                0
% 0.74/1.04  fd_pseudo_cond:                         1
% 0.74/1.04  ac_symbols:                             0
% 0.74/1.04  
% 0.74/1.04  ------ Propositional Solver
% 0.74/1.04  
% 0.74/1.04  prop_solver_calls:                      27
% 0.74/1.04  prop_fast_solver_calls:                 1869
% 0.74/1.04  smt_solver_calls:                       0
% 0.74/1.04  smt_fast_solver_calls:                  0
% 0.74/1.04  prop_num_of_clauses:                    1762
% 0.74/1.04  prop_preprocess_simplified:             6337
% 0.74/1.04  prop_fo_subsumed:                       96
% 0.74/1.04  prop_solver_time:                       0.
% 0.74/1.04  smt_solver_time:                        0.
% 0.74/1.04  smt_fast_solver_time:                   0.
% 0.74/1.04  prop_fast_solver_time:                  0.
% 0.74/1.04  prop_unsat_core_time:                   0.
% 0.74/1.04  
% 0.74/1.04  ------ QBF
% 0.74/1.04  
% 0.74/1.04  qbf_q_res:                              0
% 0.74/1.04  qbf_num_tautologies:                    0
% 0.74/1.04  qbf_prep_cycles:                        0
% 0.74/1.04  
% 0.74/1.04  ------ BMC1
% 0.74/1.04  
% 0.74/1.04  bmc1_current_bound:                     -1
% 0.74/1.04  bmc1_last_solved_bound:                 -1
% 0.74/1.04  bmc1_unsat_core_size:                   -1
% 0.74/1.04  bmc1_unsat_core_parents_size:           -1
% 0.74/1.04  bmc1_merge_next_fun:                    0
% 0.74/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.74/1.04  
% 0.74/1.04  ------ Instantiation
% 0.74/1.04  
% 0.74/1.04  inst_num_of_clauses:                    540
% 0.74/1.04  inst_num_in_passive:                    156
% 0.74/1.04  inst_num_in_active:                     284
% 0.74/1.04  inst_num_in_unprocessed:                100
% 0.74/1.04  inst_num_of_loops:                      350
% 0.74/1.04  inst_num_of_learning_restarts:          0
% 0.74/1.04  inst_num_moves_active_passive:          64
% 0.74/1.04  inst_lit_activity:                      0
% 0.74/1.04  inst_lit_activity_moves:                0
% 0.74/1.04  inst_num_tautologies:                   0
% 0.74/1.04  inst_num_prop_implied:                  0
% 0.74/1.04  inst_num_existing_simplified:           0
% 0.74/1.04  inst_num_eq_res_simplified:             0
% 0.74/1.04  inst_num_child_elim:                    0
% 0.74/1.04  inst_num_of_dismatching_blockings:      85
% 0.74/1.04  inst_num_of_non_proper_insts:           436
% 0.74/1.04  inst_num_of_duplicates:                 0
% 0.74/1.04  inst_inst_num_from_inst_to_res:         0
% 0.74/1.04  inst_dismatching_checking_time:         0.
% 0.74/1.04  
% 0.74/1.04  ------ Resolution
% 0.74/1.04  
% 0.74/1.04  res_num_of_clauses:                     0
% 0.74/1.04  res_num_in_passive:                     0
% 0.74/1.04  res_num_in_active:                      0
% 0.74/1.04  res_num_of_loops:                       175
% 0.74/1.04  res_forward_subset_subsumed:            78
% 0.74/1.04  res_backward_subset_subsumed:           0
% 0.74/1.04  res_forward_subsumed:                   0
% 0.74/1.04  res_backward_subsumed:                  0
% 0.74/1.04  res_forward_subsumption_resolution:     6
% 0.74/1.04  res_backward_subsumption_resolution:    0
% 0.74/1.04  res_clause_to_clause_subsumption:       155
% 0.74/1.04  res_orphan_elimination:                 0
% 0.74/1.04  res_tautology_del:                      49
% 0.74/1.04  res_num_eq_res_simplified:              0
% 0.74/1.04  res_num_sel_changes:                    0
% 0.74/1.04  res_moves_from_active_to_pass:          0
% 0.74/1.04  
% 0.74/1.04  ------ Superposition
% 0.74/1.04  
% 0.74/1.04  sup_time_total:                         0.
% 0.74/1.04  sup_time_generating:                    0.
% 0.74/1.04  sup_time_sim_full:                      0.
% 0.74/1.04  sup_time_sim_immed:                     0.
% 0.74/1.04  
% 0.74/1.04  sup_num_of_clauses:                     47
% 0.74/1.04  sup_num_in_active:                      42
% 0.74/1.04  sup_num_in_passive:                     5
% 0.74/1.04  sup_num_of_loops:                       68
% 0.74/1.04  sup_fw_superposition:                   43
% 0.74/1.04  sup_bw_superposition:                   6
% 0.74/1.04  sup_immediate_simplified:               6
% 0.74/1.04  sup_given_eliminated:                   0
% 0.74/1.04  comparisons_done:                       0
% 0.74/1.04  comparisons_avoided:                    0
% 0.74/1.04  
% 0.74/1.04  ------ Simplifications
% 0.74/1.04  
% 0.74/1.04  
% 0.74/1.04  sim_fw_subset_subsumed:                 1
% 0.74/1.04  sim_bw_subset_subsumed:                 12
% 0.74/1.04  sim_fw_subsumed:                        0
% 0.74/1.04  sim_bw_subsumed:                        0
% 0.74/1.04  sim_fw_subsumption_res:                 2
% 0.74/1.04  sim_bw_subsumption_res:                 0
% 0.74/1.04  sim_tautology_del:                      2
% 0.74/1.04  sim_eq_tautology_del:                   4
% 0.74/1.04  sim_eq_res_simp:                        0
% 0.74/1.04  sim_fw_demodulated:                     0
% 0.74/1.04  sim_bw_demodulated:                     17
% 0.74/1.04  sim_light_normalised:                   10
% 0.74/1.04  sim_joinable_taut:                      0
% 0.74/1.04  sim_joinable_simp:                      0
% 0.74/1.04  sim_ac_normalised:                      0
% 0.74/1.04  sim_smt_subsumption:                    0
% 0.74/1.04  
%------------------------------------------------------------------------------
