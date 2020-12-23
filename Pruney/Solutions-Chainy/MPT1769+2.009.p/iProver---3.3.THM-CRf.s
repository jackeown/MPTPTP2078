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
% DateTime   : Thu Dec  3 12:23:03 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  194 (2769 expanded)
%              Number of clauses        :  119 ( 533 expanded)
%              Number of leaves         :   19 (1090 expanded)
%              Depth                    :   20
%              Number of atoms          : 1011 (52767 expanded)
%              Number of equality atoms :  276 (3490 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f34,f41,f40,f39,f38,f37,f36,f35])).

fof(f78,plain,(
    r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    sK1 = sK4 ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f42])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6)
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6)
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3717,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f53])).

cnf(c_17,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_465,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | X3 = X0
    | u1_struct_0(sK4) != X4
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK2) != X5
    | u1_struct_0(sK2) != X2
    | sK7 != X3
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_466,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(u1_struct_0(sK2))
    | sK7 = sK5 ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_468,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | sK7 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_466,c_27,c_26,c_25,c_21,c_20,c_19])).

cnf(c_3688,plain,
    ( sK7 = sK5
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3716,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3714,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5312,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3716,c_3714])).

cnf(c_7882,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3717,c_5312])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3705,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3715,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4636,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3705,c_3715])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3720,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_248,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_249,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_248])).

cnf(c_331,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_249])).

cnf(c_3689,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_331])).

cnf(c_7350,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3720,c_3689])).

cnf(c_7473,plain,
    ( r1_tarski(sK6,X0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4636,c_7350])).

cnf(c_8003,plain,
    ( r1_tarski(sK6,X0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7882,c_7473])).

cnf(c_9034,plain,
    ( sK7 = sK5
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3688,c_8003])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3718,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9571,plain,
    ( sK7 = sK5
    | sK6 = X0
    | r1_tarski(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9034,c_3718])).

cnf(c_470,plain,
    ( sK7 = sK5
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_2806,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4084,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_2806])).

cnf(c_5061,plain,
    ( sK7 != X0
    | sK7 = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_4084])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3719,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5306,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3720,c_3719])).

cnf(c_8033,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5306,c_3719])).

cnf(c_8191,plain,
    ( r2_hidden(sK0(X0,X1),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4636,c_8033])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3721,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8421,plain,
    ( r1_tarski(X0,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) = iProver_top
    | r1_tarski(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8191,c_3721])).

cnf(c_9165,plain,
    ( r1_tarski(X0,sK6) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8421,c_5312])).

cnf(c_3708,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( sK1 = sK4 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3767,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3708,c_18])).

cnf(c_4638,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3767,c_3715])).

cnf(c_7475,plain,
    ( r1_tarski(sK7,X0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4638,c_7350])).

cnf(c_8004,plain,
    ( r1_tarski(sK7,X0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7882,c_7475])).

cnf(c_9689,plain,
    ( sK7 = sK5
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3688,c_8004])).

cnf(c_7472,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3717,c_7350])).

cnf(c_7506,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7472,c_3718])).

cnf(c_9696,plain,
    ( sK7 = X0
    | sK7 = sK5
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9689,c_7506])).

cnf(c_3702,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4637,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3702,c_3715])).

cnf(c_7474,plain,
    ( r1_tarski(sK5,X0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4637,c_7350])).

cnf(c_8005,plain,
    ( r1_tarski(sK5,X0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7882,c_7474])).

cnf(c_9812,plain,
    ( sK7 = sK5
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3688,c_8005])).

cnf(c_9819,plain,
    ( sK7 = sK5
    | sK5 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9812,c_7506])).

cnf(c_10139,plain,
    ( sK7 = sK5
    | r1_tarski(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9571,c_470,c_5061,c_9165,c_9696,c_9819])).

cnf(c_10148,plain,
    ( sK7 = sK5 ),
    inference(superposition,[status(thm)],[c_3717,c_10139])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3699,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3747,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3699,c_18])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3697,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f56])).

cnf(c_3712,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3711,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X0,X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3865,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_3712,c_3711])).

cnf(c_6084,plain,
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
    inference(superposition,[status(thm)],[c_3767,c_3865])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_41,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_42,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_43,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_54,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3707,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3756,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3707,c_18])).

cnf(c_7005,plain,
    ( v2_pre_topc(X1) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6084,c_41,c_42,c_43,c_54,c_3756])).

cnf(c_7006,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7005])).

cnf(c_7017,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(sK3)) = k3_tmap_1(X0,sK2,sK1,sK3,sK7)
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3697,c_7006])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f55])).

cnf(c_3713,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5134,plain,
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
    inference(superposition,[status(thm)],[c_3767,c_3713])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_38,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_39,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_40,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5789,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5134,c_38,c_39,c_40,c_41,c_42,c_43,c_54,c_3756])).

cnf(c_5790,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0)
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5789])).

cnf(c_5797,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(sK3)) = k2_tmap_1(sK1,sK2,sK7,sK3) ),
    inference(superposition,[status(thm)],[c_3697,c_5790])).

cnf(c_7035,plain,
    ( k3_tmap_1(X0,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3)
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7017,c_5797])).

cnf(c_8872,plain,
    ( k3_tmap_1(sK1,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3)
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3747,c_7035])).

cnf(c_8950,plain,
    ( k3_tmap_1(sK1,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8872,c_38,c_39,c_40])).

cnf(c_16,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3709,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3810,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3709,c_18])).

cnf(c_8953,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK7,sK3),sK6) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8950,c_3810])).

cnf(c_10158,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10148,c_8953])).

cnf(c_15,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3710,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3815,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3710,c_18])).

cnf(c_8954,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK7,sK3),sK6) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8950,c_3815])).

cnf(c_10159,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10148,c_8954])).

cnf(c_10179,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10158,c_10159])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:04:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.20/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.20/0.99  
% 3.20/0.99  ------  iProver source info
% 3.20/0.99  
% 3.20/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.20/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.20/0.99  git: non_committed_changes: false
% 3.20/0.99  git: last_make_outside_of_git: false
% 3.20/0.99  
% 3.20/0.99  ------ 
% 3.20/0.99  
% 3.20/0.99  ------ Input Options
% 3.20/0.99  
% 3.20/0.99  --out_options                           all
% 3.20/0.99  --tptp_safe_out                         true
% 3.20/0.99  --problem_path                          ""
% 3.20/0.99  --include_path                          ""
% 3.20/0.99  --clausifier                            res/vclausify_rel
% 3.20/0.99  --clausifier_options                    --mode clausify
% 3.20/0.99  --stdin                                 false
% 3.20/0.99  --stats_out                             all
% 3.20/0.99  
% 3.20/0.99  ------ General Options
% 3.20/0.99  
% 3.20/0.99  --fof                                   false
% 3.20/0.99  --time_out_real                         305.
% 3.20/0.99  --time_out_virtual                      -1.
% 3.20/0.99  --symbol_type_check                     false
% 3.20/0.99  --clausify_out                          false
% 3.20/0.99  --sig_cnt_out                           false
% 3.20/0.99  --trig_cnt_out                          false
% 3.20/0.99  --trig_cnt_out_tolerance                1.
% 3.20/0.99  --trig_cnt_out_sk_spl                   false
% 3.20/0.99  --abstr_cl_out                          false
% 3.20/0.99  
% 3.20/0.99  ------ Global Options
% 3.20/0.99  
% 3.20/0.99  --schedule                              default
% 3.20/0.99  --add_important_lit                     false
% 3.20/0.99  --prop_solver_per_cl                    1000
% 3.20/0.99  --min_unsat_core                        false
% 3.20/0.99  --soft_assumptions                      false
% 3.20/0.99  --soft_lemma_size                       3
% 3.20/0.99  --prop_impl_unit_size                   0
% 3.20/0.99  --prop_impl_unit                        []
% 3.20/0.99  --share_sel_clauses                     true
% 3.20/0.99  --reset_solvers                         false
% 3.20/0.99  --bc_imp_inh                            [conj_cone]
% 3.20/0.99  --conj_cone_tolerance                   3.
% 3.20/0.99  --extra_neg_conj                        none
% 3.20/0.99  --large_theory_mode                     true
% 3.20/0.99  --prolific_symb_bound                   200
% 3.20/0.99  --lt_threshold                          2000
% 3.20/0.99  --clause_weak_htbl                      true
% 3.20/0.99  --gc_record_bc_elim                     false
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing Options
% 3.20/0.99  
% 3.20/0.99  --preprocessing_flag                    true
% 3.20/0.99  --time_out_prep_mult                    0.1
% 3.20/0.99  --splitting_mode                        input
% 3.20/0.99  --splitting_grd                         true
% 3.20/0.99  --splitting_cvd                         false
% 3.20/0.99  --splitting_cvd_svl                     false
% 3.20/0.99  --splitting_nvd                         32
% 3.20/0.99  --sub_typing                            true
% 3.20/0.99  --prep_gs_sim                           true
% 3.20/0.99  --prep_unflatten                        true
% 3.20/0.99  --prep_res_sim                          true
% 3.20/0.99  --prep_upred                            true
% 3.20/0.99  --prep_sem_filter                       exhaustive
% 3.20/0.99  --prep_sem_filter_out                   false
% 3.20/0.99  --pred_elim                             true
% 3.20/0.99  --res_sim_input                         true
% 3.20/0.99  --eq_ax_congr_red                       true
% 3.20/0.99  --pure_diseq_elim                       true
% 3.20/0.99  --brand_transform                       false
% 3.20/0.99  --non_eq_to_eq                          false
% 3.20/0.99  --prep_def_merge                        true
% 3.20/0.99  --prep_def_merge_prop_impl              false
% 3.20/0.99  --prep_def_merge_mbd                    true
% 3.20/0.99  --prep_def_merge_tr_red                 false
% 3.20/0.99  --prep_def_merge_tr_cl                  false
% 3.20/0.99  --smt_preprocessing                     true
% 3.20/0.99  --smt_ac_axioms                         fast
% 3.20/0.99  --preprocessed_out                      false
% 3.20/0.99  --preprocessed_stats                    false
% 3.20/0.99  
% 3.20/0.99  ------ Abstraction refinement Options
% 3.20/0.99  
% 3.20/0.99  --abstr_ref                             []
% 3.20/0.99  --abstr_ref_prep                        false
% 3.20/0.99  --abstr_ref_until_sat                   false
% 3.20/0.99  --abstr_ref_sig_restrict                funpre
% 3.20/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.99  --abstr_ref_under                       []
% 3.20/0.99  
% 3.20/0.99  ------ SAT Options
% 3.20/0.99  
% 3.20/0.99  --sat_mode                              false
% 3.20/0.99  --sat_fm_restart_options                ""
% 3.20/0.99  --sat_gr_def                            false
% 3.20/0.99  --sat_epr_types                         true
% 3.20/0.99  --sat_non_cyclic_types                  false
% 3.20/0.99  --sat_finite_models                     false
% 3.20/0.99  --sat_fm_lemmas                         false
% 3.20/0.99  --sat_fm_prep                           false
% 3.20/0.99  --sat_fm_uc_incr                        true
% 3.20/0.99  --sat_out_model                         small
% 3.20/0.99  --sat_out_clauses                       false
% 3.20/0.99  
% 3.20/0.99  ------ QBF Options
% 3.20/0.99  
% 3.20/0.99  --qbf_mode                              false
% 3.20/0.99  --qbf_elim_univ                         false
% 3.20/0.99  --qbf_dom_inst                          none
% 3.20/0.99  --qbf_dom_pre_inst                      false
% 3.20/0.99  --qbf_sk_in                             false
% 3.20/0.99  --qbf_pred_elim                         true
% 3.20/0.99  --qbf_split                             512
% 3.20/0.99  
% 3.20/0.99  ------ BMC1 Options
% 3.20/0.99  
% 3.20/0.99  --bmc1_incremental                      false
% 3.20/0.99  --bmc1_axioms                           reachable_all
% 3.20/0.99  --bmc1_min_bound                        0
% 3.20/0.99  --bmc1_max_bound                        -1
% 3.20/0.99  --bmc1_max_bound_default                -1
% 3.20/0.99  --bmc1_symbol_reachability              true
% 3.20/0.99  --bmc1_property_lemmas                  false
% 3.20/0.99  --bmc1_k_induction                      false
% 3.20/0.99  --bmc1_non_equiv_states                 false
% 3.20/0.99  --bmc1_deadlock                         false
% 3.20/0.99  --bmc1_ucm                              false
% 3.20/0.99  --bmc1_add_unsat_core                   none
% 3.20/0.99  --bmc1_unsat_core_children              false
% 3.20/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.99  --bmc1_out_stat                         full
% 3.20/0.99  --bmc1_ground_init                      false
% 3.20/0.99  --bmc1_pre_inst_next_state              false
% 3.20/0.99  --bmc1_pre_inst_state                   false
% 3.20/0.99  --bmc1_pre_inst_reach_state             false
% 3.20/0.99  --bmc1_out_unsat_core                   false
% 3.20/0.99  --bmc1_aig_witness_out                  false
% 3.20/0.99  --bmc1_verbose                          false
% 3.20/0.99  --bmc1_dump_clauses_tptp                false
% 3.20/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.99  --bmc1_dump_file                        -
% 3.20/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.99  --bmc1_ucm_extend_mode                  1
% 3.20/0.99  --bmc1_ucm_init_mode                    2
% 3.20/0.99  --bmc1_ucm_cone_mode                    none
% 3.20/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.99  --bmc1_ucm_relax_model                  4
% 3.20/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.99  --bmc1_ucm_layered_model                none
% 3.20/0.99  --bmc1_ucm_max_lemma_size               10
% 3.20/0.99  
% 3.20/0.99  ------ AIG Options
% 3.20/0.99  
% 3.20/0.99  --aig_mode                              false
% 3.20/0.99  
% 3.20/0.99  ------ Instantiation Options
% 3.20/0.99  
% 3.20/0.99  --instantiation_flag                    true
% 3.20/0.99  --inst_sos_flag                         false
% 3.20/0.99  --inst_sos_phase                        true
% 3.20/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel_side                     num_symb
% 3.20/0.99  --inst_solver_per_active                1400
% 3.20/0.99  --inst_solver_calls_frac                1.
% 3.20/0.99  --inst_passive_queue_type               priority_queues
% 3.20/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.99  --inst_passive_queues_freq              [25;2]
% 3.20/0.99  --inst_dismatching                      true
% 3.20/0.99  --inst_eager_unprocessed_to_passive     true
% 3.20/0.99  --inst_prop_sim_given                   true
% 3.20/0.99  --inst_prop_sim_new                     false
% 3.20/0.99  --inst_subs_new                         false
% 3.20/0.99  --inst_eq_res_simp                      false
% 3.20/0.99  --inst_subs_given                       false
% 3.20/0.99  --inst_orphan_elimination               true
% 3.20/0.99  --inst_learning_loop_flag               true
% 3.20/0.99  --inst_learning_start                   3000
% 3.20/0.99  --inst_learning_factor                  2
% 3.20/0.99  --inst_start_prop_sim_after_learn       3
% 3.20/0.99  --inst_sel_renew                        solver
% 3.20/0.99  --inst_lit_activity_flag                true
% 3.20/0.99  --inst_restr_to_given                   false
% 3.20/0.99  --inst_activity_threshold               500
% 3.20/0.99  --inst_out_proof                        true
% 3.20/0.99  
% 3.20/0.99  ------ Resolution Options
% 3.20/0.99  
% 3.20/0.99  --resolution_flag                       true
% 3.20/0.99  --res_lit_sel                           adaptive
% 3.20/0.99  --res_lit_sel_side                      none
% 3.20/0.99  --res_ordering                          kbo
% 3.20/0.99  --res_to_prop_solver                    active
% 3.20/0.99  --res_prop_simpl_new                    false
% 3.20/0.99  --res_prop_simpl_given                  true
% 3.20/0.99  --res_passive_queue_type                priority_queues
% 3.20/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.99  --res_passive_queues_freq               [15;5]
% 3.20/0.99  --res_forward_subs                      full
% 3.20/0.99  --res_backward_subs                     full
% 3.20/0.99  --res_forward_subs_resolution           true
% 3.20/0.99  --res_backward_subs_resolution          true
% 3.20/0.99  --res_orphan_elimination                true
% 3.20/0.99  --res_time_limit                        2.
% 3.20/0.99  --res_out_proof                         true
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Options
% 3.20/0.99  
% 3.20/0.99  --superposition_flag                    true
% 3.20/0.99  --sup_passive_queue_type                priority_queues
% 3.20/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.99  --demod_completeness_check              fast
% 3.20/0.99  --demod_use_ground                      true
% 3.20/0.99  --sup_to_prop_solver                    passive
% 3.20/0.99  --sup_prop_simpl_new                    true
% 3.20/0.99  --sup_prop_simpl_given                  true
% 3.20/0.99  --sup_fun_splitting                     false
% 3.20/0.99  --sup_smt_interval                      50000
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Simplification Setup
% 3.20/0.99  
% 3.20/0.99  --sup_indices_passive                   []
% 3.20/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_full_bw                           [BwDemod]
% 3.20/0.99  --sup_immed_triv                        [TrivRules]
% 3.20/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_immed_bw_main                     []
% 3.20/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.99  
% 3.20/0.99  ------ Combination Options
% 3.20/0.99  
% 3.20/0.99  --comb_res_mult                         3
% 3.20/0.99  --comb_sup_mult                         2
% 3.20/0.99  --comb_inst_mult                        10
% 3.20/0.99  
% 3.20/0.99  ------ Debug Options
% 3.20/0.99  
% 3.20/0.99  --dbg_backtrace                         false
% 3.20/0.99  --dbg_dump_prop_clauses                 false
% 3.20/0.99  --dbg_dump_prop_clauses_file            -
% 3.20/0.99  --dbg_out_stat                          false
% 3.20/0.99  ------ Parsing...
% 3.20/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.20/0.99  ------ Proving...
% 3.20/0.99  ------ Problem Properties 
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  clauses                                 35
% 3.20/0.99  conjectures                             22
% 3.20/0.99  EPR                                     19
% 3.20/0.99  Horn                                    30
% 3.20/0.99  unary                                   21
% 3.20/0.99  binary                                  7
% 3.20/0.99  lits                                    76
% 3.20/0.99  lits eq                                 5
% 3.20/0.99  fd_pure                                 0
% 3.20/0.99  fd_pseudo                               0
% 3.20/0.99  fd_cond                                 0
% 3.20/0.99  fd_pseudo_cond                          1
% 3.20/0.99  AC symbols                              0
% 3.20/0.99  
% 3.20/0.99  ------ Schedule dynamic 5 is on 
% 3.20/0.99  
% 3.20/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  ------ 
% 3.20/0.99  Current options:
% 3.20/0.99  ------ 
% 3.20/0.99  
% 3.20/0.99  ------ Input Options
% 3.20/0.99  
% 3.20/0.99  --out_options                           all
% 3.20/0.99  --tptp_safe_out                         true
% 3.20/0.99  --problem_path                          ""
% 3.20/0.99  --include_path                          ""
% 3.20/0.99  --clausifier                            res/vclausify_rel
% 3.20/0.99  --clausifier_options                    --mode clausify
% 3.20/0.99  --stdin                                 false
% 3.20/0.99  --stats_out                             all
% 3.20/0.99  
% 3.20/0.99  ------ General Options
% 3.20/0.99  
% 3.20/0.99  --fof                                   false
% 3.20/0.99  --time_out_real                         305.
% 3.20/0.99  --time_out_virtual                      -1.
% 3.20/0.99  --symbol_type_check                     false
% 3.20/0.99  --clausify_out                          false
% 3.20/0.99  --sig_cnt_out                           false
% 3.20/0.99  --trig_cnt_out                          false
% 3.20/0.99  --trig_cnt_out_tolerance                1.
% 3.20/0.99  --trig_cnt_out_sk_spl                   false
% 3.20/0.99  --abstr_cl_out                          false
% 3.20/0.99  
% 3.20/0.99  ------ Global Options
% 3.20/0.99  
% 3.20/0.99  --schedule                              default
% 3.20/0.99  --add_important_lit                     false
% 3.20/0.99  --prop_solver_per_cl                    1000
% 3.20/0.99  --min_unsat_core                        false
% 3.20/0.99  --soft_assumptions                      false
% 3.20/0.99  --soft_lemma_size                       3
% 3.20/0.99  --prop_impl_unit_size                   0
% 3.20/0.99  --prop_impl_unit                        []
% 3.20/0.99  --share_sel_clauses                     true
% 3.20/0.99  --reset_solvers                         false
% 3.20/0.99  --bc_imp_inh                            [conj_cone]
% 3.20/0.99  --conj_cone_tolerance                   3.
% 3.20/0.99  --extra_neg_conj                        none
% 3.20/0.99  --large_theory_mode                     true
% 3.20/0.99  --prolific_symb_bound                   200
% 3.20/0.99  --lt_threshold                          2000
% 3.20/0.99  --clause_weak_htbl                      true
% 3.20/0.99  --gc_record_bc_elim                     false
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing Options
% 3.20/0.99  
% 3.20/0.99  --preprocessing_flag                    true
% 3.20/0.99  --time_out_prep_mult                    0.1
% 3.20/0.99  --splitting_mode                        input
% 3.20/0.99  --splitting_grd                         true
% 3.20/0.99  --splitting_cvd                         false
% 3.20/0.99  --splitting_cvd_svl                     false
% 3.20/0.99  --splitting_nvd                         32
% 3.20/0.99  --sub_typing                            true
% 3.20/0.99  --prep_gs_sim                           true
% 3.20/0.99  --prep_unflatten                        true
% 3.20/0.99  --prep_res_sim                          true
% 3.20/0.99  --prep_upred                            true
% 3.20/0.99  --prep_sem_filter                       exhaustive
% 3.20/0.99  --prep_sem_filter_out                   false
% 3.20/0.99  --pred_elim                             true
% 3.20/0.99  --res_sim_input                         true
% 3.20/0.99  --eq_ax_congr_red                       true
% 3.20/0.99  --pure_diseq_elim                       true
% 3.20/0.99  --brand_transform                       false
% 3.20/0.99  --non_eq_to_eq                          false
% 3.20/0.99  --prep_def_merge                        true
% 3.20/0.99  --prep_def_merge_prop_impl              false
% 3.20/0.99  --prep_def_merge_mbd                    true
% 3.20/0.99  --prep_def_merge_tr_red                 false
% 3.20/0.99  --prep_def_merge_tr_cl                  false
% 3.20/0.99  --smt_preprocessing                     true
% 3.20/0.99  --smt_ac_axioms                         fast
% 3.20/0.99  --preprocessed_out                      false
% 3.20/0.99  --preprocessed_stats                    false
% 3.20/0.99  
% 3.20/0.99  ------ Abstraction refinement Options
% 3.20/0.99  
% 3.20/0.99  --abstr_ref                             []
% 3.20/0.99  --abstr_ref_prep                        false
% 3.20/0.99  --abstr_ref_until_sat                   false
% 3.20/0.99  --abstr_ref_sig_restrict                funpre
% 3.20/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.99  --abstr_ref_under                       []
% 3.20/0.99  
% 3.20/0.99  ------ SAT Options
% 3.20/0.99  
% 3.20/0.99  --sat_mode                              false
% 3.20/0.99  --sat_fm_restart_options                ""
% 3.20/0.99  --sat_gr_def                            false
% 3.20/0.99  --sat_epr_types                         true
% 3.20/0.99  --sat_non_cyclic_types                  false
% 3.20/0.99  --sat_finite_models                     false
% 3.20/0.99  --sat_fm_lemmas                         false
% 3.20/0.99  --sat_fm_prep                           false
% 3.20/0.99  --sat_fm_uc_incr                        true
% 3.20/0.99  --sat_out_model                         small
% 3.20/0.99  --sat_out_clauses                       false
% 3.20/0.99  
% 3.20/0.99  ------ QBF Options
% 3.20/0.99  
% 3.20/0.99  --qbf_mode                              false
% 3.20/0.99  --qbf_elim_univ                         false
% 3.20/0.99  --qbf_dom_inst                          none
% 3.20/0.99  --qbf_dom_pre_inst                      false
% 3.20/0.99  --qbf_sk_in                             false
% 3.20/0.99  --qbf_pred_elim                         true
% 3.20/0.99  --qbf_split                             512
% 3.20/0.99  
% 3.20/0.99  ------ BMC1 Options
% 3.20/0.99  
% 3.20/0.99  --bmc1_incremental                      false
% 3.20/0.99  --bmc1_axioms                           reachable_all
% 3.20/0.99  --bmc1_min_bound                        0
% 3.20/0.99  --bmc1_max_bound                        -1
% 3.20/0.99  --bmc1_max_bound_default                -1
% 3.20/0.99  --bmc1_symbol_reachability              true
% 3.20/0.99  --bmc1_property_lemmas                  false
% 3.20/0.99  --bmc1_k_induction                      false
% 3.20/0.99  --bmc1_non_equiv_states                 false
% 3.20/0.99  --bmc1_deadlock                         false
% 3.20/0.99  --bmc1_ucm                              false
% 3.20/0.99  --bmc1_add_unsat_core                   none
% 3.20/0.99  --bmc1_unsat_core_children              false
% 3.20/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.99  --bmc1_out_stat                         full
% 3.20/0.99  --bmc1_ground_init                      false
% 3.20/0.99  --bmc1_pre_inst_next_state              false
% 3.20/0.99  --bmc1_pre_inst_state                   false
% 3.20/0.99  --bmc1_pre_inst_reach_state             false
% 3.20/0.99  --bmc1_out_unsat_core                   false
% 3.20/0.99  --bmc1_aig_witness_out                  false
% 3.20/0.99  --bmc1_verbose                          false
% 3.20/0.99  --bmc1_dump_clauses_tptp                false
% 3.20/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.99  --bmc1_dump_file                        -
% 3.20/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.99  --bmc1_ucm_extend_mode                  1
% 3.20/0.99  --bmc1_ucm_init_mode                    2
% 3.20/0.99  --bmc1_ucm_cone_mode                    none
% 3.20/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.99  --bmc1_ucm_relax_model                  4
% 3.20/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.99  --bmc1_ucm_layered_model                none
% 3.20/0.99  --bmc1_ucm_max_lemma_size               10
% 3.20/0.99  
% 3.20/0.99  ------ AIG Options
% 3.20/0.99  
% 3.20/0.99  --aig_mode                              false
% 3.20/0.99  
% 3.20/0.99  ------ Instantiation Options
% 3.20/0.99  
% 3.20/0.99  --instantiation_flag                    true
% 3.20/0.99  --inst_sos_flag                         false
% 3.20/0.99  --inst_sos_phase                        true
% 3.20/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel_side                     none
% 3.20/0.99  --inst_solver_per_active                1400
% 3.20/0.99  --inst_solver_calls_frac                1.
% 3.20/0.99  --inst_passive_queue_type               priority_queues
% 3.20/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.99  --inst_passive_queues_freq              [25;2]
% 3.20/0.99  --inst_dismatching                      true
% 3.20/0.99  --inst_eager_unprocessed_to_passive     true
% 3.20/0.99  --inst_prop_sim_given                   true
% 3.20/0.99  --inst_prop_sim_new                     false
% 3.20/0.99  --inst_subs_new                         false
% 3.20/0.99  --inst_eq_res_simp                      false
% 3.20/0.99  --inst_subs_given                       false
% 3.20/0.99  --inst_orphan_elimination               true
% 3.20/0.99  --inst_learning_loop_flag               true
% 3.20/0.99  --inst_learning_start                   3000
% 3.20/0.99  --inst_learning_factor                  2
% 3.20/0.99  --inst_start_prop_sim_after_learn       3
% 3.20/0.99  --inst_sel_renew                        solver
% 3.20/0.99  --inst_lit_activity_flag                true
% 3.20/0.99  --inst_restr_to_given                   false
% 3.20/0.99  --inst_activity_threshold               500
% 3.20/0.99  --inst_out_proof                        true
% 3.20/0.99  
% 3.20/0.99  ------ Resolution Options
% 3.20/0.99  
% 3.20/0.99  --resolution_flag                       false
% 3.20/0.99  --res_lit_sel                           adaptive
% 3.20/0.99  --res_lit_sel_side                      none
% 3.20/0.99  --res_ordering                          kbo
% 3.20/0.99  --res_to_prop_solver                    active
% 3.20/0.99  --res_prop_simpl_new                    false
% 3.20/0.99  --res_prop_simpl_given                  true
% 3.20/0.99  --res_passive_queue_type                priority_queues
% 3.20/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.99  --res_passive_queues_freq               [15;5]
% 3.20/0.99  --res_forward_subs                      full
% 3.20/0.99  --res_backward_subs                     full
% 3.20/0.99  --res_forward_subs_resolution           true
% 3.20/0.99  --res_backward_subs_resolution          true
% 3.20/0.99  --res_orphan_elimination                true
% 3.20/0.99  --res_time_limit                        2.
% 3.20/0.99  --res_out_proof                         true
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Options
% 3.20/0.99  
% 3.20/0.99  --superposition_flag                    true
% 3.20/0.99  --sup_passive_queue_type                priority_queues
% 3.20/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.99  --demod_completeness_check              fast
% 3.20/0.99  --demod_use_ground                      true
% 3.20/0.99  --sup_to_prop_solver                    passive
% 3.20/0.99  --sup_prop_simpl_new                    true
% 3.20/0.99  --sup_prop_simpl_given                  true
% 3.20/0.99  --sup_fun_splitting                     false
% 3.20/0.99  --sup_smt_interval                      50000
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Simplification Setup
% 3.20/0.99  
% 3.20/0.99  --sup_indices_passive                   []
% 3.20/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_full_bw                           [BwDemod]
% 3.20/0.99  --sup_immed_triv                        [TrivRules]
% 3.20/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_immed_bw_main                     []
% 3.20/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.99  
% 3.20/0.99  ------ Combination Options
% 3.20/0.99  
% 3.20/0.99  --comb_res_mult                         3
% 3.20/0.99  --comb_sup_mult                         2
% 3.20/0.99  --comb_inst_mult                        10
% 3.20/0.99  
% 3.20/0.99  ------ Debug Options
% 3.20/0.99  
% 3.20/0.99  --dbg_backtrace                         false
% 3.20/0.99  --dbg_dump_prop_clauses                 false
% 3.20/0.99  --dbg_dump_prop_clauses_file            -
% 3.20/0.99  --dbg_out_stat                          false
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  ------ Proving...
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  % SZS status Theorem for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99   Resolution empty clause
% 3.20/0.99  
% 3.20/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  fof(f2,axiom,(
% 3.20/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f29,plain,(
% 3.20/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.20/0.99    inference(nnf_transformation,[],[f2])).
% 3.20/0.99  
% 3.20/0.99  fof(f30,plain,(
% 3.20/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.20/0.99    inference(flattening,[],[f29])).
% 3.20/0.99  
% 3.20/0.99  fof(f46,plain,(
% 3.20/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.20/0.99    inference(cnf_transformation,[],[f30])).
% 3.20/0.99  
% 3.20/0.99  fof(f82,plain,(
% 3.20/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.20/0.99    inference(equality_resolution,[],[f46])).
% 3.20/0.99  
% 3.20/0.99  fof(f6,axiom,(
% 3.20/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f15,plain,(
% 3.20/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.20/0.99    inference(ennf_transformation,[],[f6])).
% 3.20/0.99  
% 3.20/0.99  fof(f16,plain,(
% 3.20/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.20/0.99    inference(flattening,[],[f15])).
% 3.20/0.99  
% 3.20/0.99  fof(f32,plain,(
% 3.20/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.20/0.99    inference(nnf_transformation,[],[f16])).
% 3.20/0.99  
% 3.20/0.99  fof(f53,plain,(
% 3.20/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f32])).
% 3.20/0.99  
% 3.20/0.99  fof(f10,conjecture,(
% 3.20/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f11,negated_conjecture,(
% 3.20/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 3.20/0.99    inference(negated_conjecture,[],[f10])).
% 3.20/0.99  
% 3.20/0.99  fof(f23,plain,(
% 3.20/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.20/0.99    inference(ennf_transformation,[],[f11])).
% 3.20/0.99  
% 3.20/0.99  fof(f24,plain,(
% 3.20/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.20/0.99    inference(flattening,[],[f23])).
% 3.20/0.99  
% 3.20/0.99  fof(f33,plain,(
% 3.20/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.20/0.99    inference(nnf_transformation,[],[f24])).
% 3.20/0.99  
% 3.20/0.99  fof(f34,plain,(
% 3.20/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.20/0.99    inference(flattening,[],[f33])).
% 3.20/0.99  
% 3.20/0.99  fof(f41,plain,(
% 3.20/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK7),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK7),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK7) & X0 = X3 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 3.20/0.99    introduced(choice_axiom,[])).
% 3.20/0.99  
% 3.20/0.99  fof(f40,plain,(
% 3.20/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK6) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK6)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK6) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK6)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 3.20/0.99    introduced(choice_axiom,[])).
% 3.20/0.99  
% 3.20/0.99  fof(f39,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK5,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK5,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK5,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 3.20/0.99    introduced(choice_axiom,[])).
% 3.20/0.99  
% 3.20/0.99  fof(f38,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK4),u1_struct_0(X1),X4,X6) & sK4 = X0 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.20/0.99    introduced(choice_axiom,[])).
% 3.20/0.99  
% 3.20/0.99  fof(f37,plain,(
% 3.20/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK3),X5) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X6),X5)) & (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK3),X5) | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.20/0.99    introduced(choice_axiom,[])).
% 3.20/0.99  
% 3.20/0.99  fof(f36,plain,(
% 3.20/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X3),u1_struct_0(sK2),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 3.20/0.99    introduced(choice_axiom,[])).
% 3.20/0.99  
% 3.20/0.99  fof(f35,plain,(
% 3.20/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK1,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK1,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK1),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK1 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.20/0.99    introduced(choice_axiom,[])).
% 3.20/0.99  
% 3.20/0.99  fof(f42,plain,(
% 3.20/0.99    (((((((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)) & (r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)) & r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) & sK1 = sK4 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.20/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f34,f41,f40,f39,f38,f37,f36,f35])).
% 3.20/0.99  
% 3.20/0.99  fof(f78,plain,(
% 3.20/0.99    r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f68,plain,(
% 3.20/0.99    v1_funct_1(sK5)),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f69,plain,(
% 3.20/0.99    v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f70,plain,(
% 3.20/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f74,plain,(
% 3.20/0.99    v1_funct_1(sK7)),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f75,plain,(
% 3.20/0.99    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2))),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f76,plain,(
% 3.20/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f3,axiom,(
% 3.20/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f31,plain,(
% 3.20/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.20/0.99    inference(nnf_transformation,[],[f3])).
% 3.20/0.99  
% 3.20/0.99  fof(f50,plain,(
% 3.20/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f31])).
% 3.20/0.99  
% 3.20/0.99  fof(f5,axiom,(
% 3.20/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f14,plain,(
% 3.20/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.20/0.99    inference(ennf_transformation,[],[f5])).
% 3.20/0.99  
% 3.20/0.99  fof(f52,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f14])).
% 3.20/0.99  
% 3.20/0.99  fof(f73,plain,(
% 3.20/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f49,plain,(
% 3.20/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f31])).
% 3.20/0.99  
% 3.20/0.99  fof(f1,axiom,(
% 3.20/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f12,plain,(
% 3.20/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.20/0.99    inference(ennf_transformation,[],[f1])).
% 3.20/0.99  
% 3.20/0.99  fof(f25,plain,(
% 3.20/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.20/0.99    inference(nnf_transformation,[],[f12])).
% 3.20/0.99  
% 3.20/0.99  fof(f26,plain,(
% 3.20/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.20/0.99    inference(rectify,[],[f25])).
% 3.20/0.99  
% 3.20/0.99  fof(f27,plain,(
% 3.20/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.20/0.99    introduced(choice_axiom,[])).
% 3.20/0.99  
% 3.20/0.99  fof(f28,plain,(
% 3.20/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.20/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.20/0.99  
% 3.20/0.99  fof(f44,plain,(
% 3.20/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f28])).
% 3.20/0.99  
% 3.20/0.99  fof(f4,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f13,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.20/0.99    inference(ennf_transformation,[],[f4])).
% 3.20/0.99  
% 3.20/0.99  fof(f51,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f13])).
% 3.20/0.99  
% 3.20/0.99  fof(f48,plain,(
% 3.20/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f30])).
% 3.20/0.99  
% 3.20/0.99  fof(f43,plain,(
% 3.20/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f28])).
% 3.20/0.99  
% 3.20/0.99  fof(f45,plain,(
% 3.20/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f28])).
% 3.20/0.99  
% 3.20/0.99  fof(f77,plain,(
% 3.20/0.99    sK1 = sK4),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f67,plain,(
% 3.20/0.99    m1_pre_topc(sK4,sK1)),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f65,plain,(
% 3.20/0.99    m1_pre_topc(sK3,sK1)),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f8,axiom,(
% 3.20/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f19,plain,(
% 3.20/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.20/0.99    inference(ennf_transformation,[],[f8])).
% 3.20/0.99  
% 3.20/0.99  fof(f20,plain,(
% 3.20/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.20/0.99    inference(flattening,[],[f19])).
% 3.20/0.99  
% 3.20/0.99  fof(f56,plain,(
% 3.20/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f20])).
% 3.20/0.99  
% 3.20/0.99  fof(f9,axiom,(
% 3.20/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f21,plain,(
% 3.20/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.20/0.99    inference(ennf_transformation,[],[f9])).
% 3.20/0.99  
% 3.20/0.99  fof(f22,plain,(
% 3.20/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.20/0.99    inference(flattening,[],[f21])).
% 3.20/0.99  
% 3.20/0.99  fof(f57,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f22])).
% 3.20/0.99  
% 3.20/0.99  fof(f61,plain,(
% 3.20/0.99    ~v2_struct_0(sK2)),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f62,plain,(
% 3.20/0.99    v2_pre_topc(sK2)),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f63,plain,(
% 3.20/0.99    l1_pre_topc(sK2)),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f7,axiom,(
% 3.20/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f17,plain,(
% 3.20/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.20/0.99    inference(ennf_transformation,[],[f7])).
% 3.20/0.99  
% 3.20/0.99  fof(f18,plain,(
% 3.20/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.20/0.99    inference(flattening,[],[f17])).
% 3.20/0.99  
% 3.20/0.99  fof(f55,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f18])).
% 3.20/0.99  
% 3.20/0.99  fof(f58,plain,(
% 3.20/0.99    ~v2_struct_0(sK1)),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f59,plain,(
% 3.20/0.99    v2_pre_topc(sK1)),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f60,plain,(
% 3.20/0.99    l1_pre_topc(sK1)),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f79,plain,(
% 3.20/0.99    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f80,plain,(
% 3.20/0.99    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f82]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3717,plain,
% 3.20/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_11,plain,
% 3.20/0.99      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 3.20/0.99      | ~ v1_funct_2(X5,X2,X3)
% 3.20/0.99      | ~ v1_funct_2(X4,X0,X1)
% 3.20/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.20/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.20/0.99      | ~ v1_funct_1(X5)
% 3.20/0.99      | ~ v1_funct_1(X4)
% 3.20/0.99      | v1_xboole_0(X1)
% 3.20/0.99      | v1_xboole_0(X3)
% 3.20/0.99      | X4 = X5 ),
% 3.20/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_17,negated_conjecture,
% 3.20/0.99      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) ),
% 3.20/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_465,plain,
% 3.20/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.20/0.99      | ~ v1_funct_2(X3,X4,X5)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.20/0.99      | ~ v1_funct_1(X0)
% 3.20/0.99      | ~ v1_funct_1(X3)
% 3.20/0.99      | v1_xboole_0(X5)
% 3.20/0.99      | v1_xboole_0(X2)
% 3.20/0.99      | X3 = X0
% 3.20/0.99      | u1_struct_0(sK4) != X4
% 3.20/0.99      | u1_struct_0(sK1) != X1
% 3.20/0.99      | u1_struct_0(sK2) != X5
% 3.20/0.99      | u1_struct_0(sK2) != X2
% 3.20/0.99      | sK7 != X3
% 3.20/0.99      | sK5 != X0 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_466,plain,
% 3.20/0.99      ( ~ v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2))
% 3.20/0.99      | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
% 3.20/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 3.20/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 3.20/0.99      | ~ v1_funct_1(sK7)
% 3.20/0.99      | ~ v1_funct_1(sK5)
% 3.20/0.99      | v1_xboole_0(u1_struct_0(sK2))
% 3.20/0.99      | sK7 = sK5 ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_465]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_27,negated_conjecture,
% 3.20/0.99      ( v1_funct_1(sK5) ),
% 3.20/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_26,negated_conjecture,
% 3.20/0.99      ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_25,negated_conjecture,
% 3.20/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 3.20/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_21,negated_conjecture,
% 3.20/0.99      ( v1_funct_1(sK7) ),
% 3.20/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_20,negated_conjecture,
% 3.20/0.99      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_19,negated_conjecture,
% 3.20/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 3.20/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_468,plain,
% 3.20/0.99      ( v1_xboole_0(u1_struct_0(sK2)) | sK7 = sK5 ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_466,c_27,c_26,c_25,c_21,c_20,c_19]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3688,plain,
% 3.20/0.99      ( sK7 = sK5 | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6,plain,
% 3.20/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3716,plain,
% 3.20/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.20/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_9,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | ~ v1_xboole_0(X2)
% 3.20/0.99      | v1_xboole_0(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3714,plain,
% 3.20/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.20/0.99      | v1_xboole_0(X2) != iProver_top
% 3.20/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5312,plain,
% 3.20/0.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.20/0.99      | v1_xboole_0(X2) != iProver_top
% 3.20/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3716,c_3714]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7882,plain,
% 3.20/0.99      ( v1_xboole_0(X0) != iProver_top
% 3.20/0.99      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3717,c_5312]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_22,negated_conjecture,
% 3.20/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 3.20/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3705,plain,
% 3.20/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3715,plain,
% 3.20/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.20/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4636,plain,
% 3.20/0.99      ( r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3705,c_3715]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1,plain,
% 3.20/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3720,plain,
% 3.20/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.20/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_8,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.20/0.99      | ~ r2_hidden(X2,X0)
% 3.20/0.99      | ~ v1_xboole_0(X1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_248,plain,
% 3.20/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.20/0.99      inference(prop_impl,[status(thm)],[c_6]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_249,plain,
% 3.20/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_248]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_331,plain,
% 3.20/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 3.20/0.99      inference(bin_hyper_res,[status(thm)],[c_8,c_249]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3689,plain,
% 3.20/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.20/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.20/0.99      | v1_xboole_0(X2) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_331]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7350,plain,
% 3.20/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.20/0.99      | r1_tarski(X0,X2) = iProver_top
% 3.20/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3720,c_3689]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7473,plain,
% 3.20/0.99      ( r1_tarski(sK6,X0) = iProver_top
% 3.20/0.99      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_4636,c_7350]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_8003,plain,
% 3.20/0.99      ( r1_tarski(sK6,X0) = iProver_top
% 3.20/0.99      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_7882,c_7473]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_9034,plain,
% 3.20/0.99      ( sK7 = sK5 | r1_tarski(sK6,X0) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3688,c_8003]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3,plain,
% 3.20/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.20/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3718,plain,
% 3.20/0.99      ( X0 = X1
% 3.20/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.20/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_9571,plain,
% 3.20/0.99      ( sK7 = sK5 | sK6 = X0 | r1_tarski(X0,sK6) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_9034,c_3718]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_470,plain,
% 3.20/0.99      ( sK7 = sK5 | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2806,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4084,plain,
% 3.20/0.99      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_2806]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5061,plain,
% 3.20/0.99      ( sK7 != X0 | sK7 = sK5 | sK5 != X0 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_4084]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2,plain,
% 3.20/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.20/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3719,plain,
% 3.20/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.20/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.20/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5306,plain,
% 3.20/0.99      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 3.20/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.20/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3720,c_3719]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_8033,plain,
% 3.20/0.99      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 3.20/0.99      | r1_tarski(X0,X3) != iProver_top
% 3.20/0.99      | r1_tarski(X3,X2) != iProver_top
% 3.20/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_5306,c_3719]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_8191,plain,
% 3.20/0.99      ( r2_hidden(sK0(X0,X1),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) = iProver_top
% 3.20/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.20/0.99      | r1_tarski(X0,sK6) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_4636,c_8033]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_0,plain,
% 3.20/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3721,plain,
% 3.20/0.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.20/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_8421,plain,
% 3.20/0.99      ( r1_tarski(X0,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) = iProver_top
% 3.20/0.99      | r1_tarski(X0,sK6) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_8191,c_3721]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_9165,plain,
% 3.20/0.99      ( r1_tarski(X0,sK6) != iProver_top
% 3.20/0.99      | v1_xboole_0(X0) = iProver_top
% 3.20/0.99      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_8421,c_5312]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3708,plain,
% 3.20/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_18,negated_conjecture,
% 3.20/0.99      ( sK1 = sK4 ),
% 3.20/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3767,plain,
% 3.20/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_3708,c_18]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4638,plain,
% 3.20/0.99      ( r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3767,c_3715]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7475,plain,
% 3.20/0.99      ( r1_tarski(sK7,X0) = iProver_top
% 3.20/0.99      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_4638,c_7350]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_8004,plain,
% 3.20/0.99      ( r1_tarski(sK7,X0) = iProver_top
% 3.20/0.99      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_7882,c_7475]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_9689,plain,
% 3.20/0.99      ( sK7 = sK5 | r1_tarski(sK7,X0) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3688,c_8004]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7472,plain,
% 3.20/0.99      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3717,c_7350]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7506,plain,
% 3.20/0.99      ( X0 = X1
% 3.20/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.20/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_7472,c_3718]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_9696,plain,
% 3.20/0.99      ( sK7 = X0 | sK7 = sK5 | v1_xboole_0(X0) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_9689,c_7506]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3702,plain,
% 3.20/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4637,plain,
% 3.20/0.99      ( r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3702,c_3715]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7474,plain,
% 3.20/0.99      ( r1_tarski(sK5,X0) = iProver_top
% 3.20/0.99      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_4637,c_7350]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_8005,plain,
% 3.20/0.99      ( r1_tarski(sK5,X0) = iProver_top
% 3.20/0.99      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_7882,c_7474]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_9812,plain,
% 3.20/0.99      ( sK7 = sK5 | r1_tarski(sK5,X0) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3688,c_8005]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_9819,plain,
% 3.20/0.99      ( sK7 = sK5 | sK5 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_9812,c_7506]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_10139,plain,
% 3.20/0.99      ( sK7 = sK5 | r1_tarski(X0,sK6) != iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_9571,c_470,c_5061,c_9165,c_9696,c_9819]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_10148,plain,
% 3.20/0.99      ( sK7 = sK5 ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3717,c_10139]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_28,negated_conjecture,
% 3.20/0.99      ( m1_pre_topc(sK4,sK1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3699,plain,
% 3.20/0.99      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3747,plain,
% 3.20/0.99      ( m1_pre_topc(sK1,sK1) = iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_3699,c_18]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_30,negated_conjecture,
% 3.20/0.99      ( m1_pre_topc(sK3,sK1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3697,plain,
% 3.20/0.99      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_13,plain,
% 3.20/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.20/0.99      | ~ m1_pre_topc(X3,X4)
% 3.20/0.99      | ~ m1_pre_topc(X3,X1)
% 3.20/0.99      | ~ m1_pre_topc(X1,X4)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.20/0.99      | v2_struct_0(X4)
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ v2_pre_topc(X4)
% 3.20/0.99      | ~ l1_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X4)
% 3.20/0.99      | ~ v1_funct_1(X0)
% 3.20/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3712,plain,
% 3.20/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
% 3.20/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.20/0.99      | m1_pre_topc(X3,X4) != iProver_top
% 3.20/0.99      | m1_pre_topc(X3,X0) != iProver_top
% 3.20/0.99      | m1_pre_topc(X0,X4) != iProver_top
% 3.20/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.20/0.99      | v2_struct_0(X4) = iProver_top
% 3.20/0.99      | v2_struct_0(X1) = iProver_top
% 3.20/0.99      | v2_pre_topc(X1) != iProver_top
% 3.20/0.99      | v2_pre_topc(X4) != iProver_top
% 3.20/0.99      | l1_pre_topc(X1) != iProver_top
% 3.20/0.99      | l1_pre_topc(X4) != iProver_top
% 3.20/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_14,plain,
% 3.20/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.20/0.99      | ~ m1_pre_topc(X1,X2)
% 3.20/0.99      | m1_pre_topc(X0,X2)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X2) ),
% 3.20/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3711,plain,
% 3.20/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1,X2) != iProver_top
% 3.20/0.99      | m1_pre_topc(X0,X2) = iProver_top
% 3.20/0.99      | v2_pre_topc(X2) != iProver_top
% 3.20/0.99      | l1_pre_topc(X2) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3865,plain,
% 3.20/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
% 3.20/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.20/0.99      | m1_pre_topc(X3,X0) != iProver_top
% 3.20/0.99      | m1_pre_topc(X0,X4) != iProver_top
% 3.20/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.20/0.99      | v2_struct_0(X4) = iProver_top
% 3.20/0.99      | v2_struct_0(X1) = iProver_top
% 3.20/0.99      | v2_pre_topc(X4) != iProver_top
% 3.20/0.99      | v2_pre_topc(X1) != iProver_top
% 3.20/0.99      | l1_pre_topc(X4) != iProver_top
% 3.20/0.99      | l1_pre_topc(X1) != iProver_top
% 3.20/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.20/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3712,c_3711]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6084,plain,
% 3.20/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
% 3.20/0.99      | v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 3.20/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.20/0.99      | m1_pre_topc(sK1,X1) != iProver_top
% 3.20/0.99      | v2_struct_0(X1) = iProver_top
% 3.20/0.99      | v2_struct_0(sK2) = iProver_top
% 3.20/0.99      | v2_pre_topc(X1) != iProver_top
% 3.20/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.20/0.99      | l1_pre_topc(X1) != iProver_top
% 3.20/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.20/0.99      | v1_funct_1(sK7) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3767,c_3865]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_34,negated_conjecture,
% 3.20/0.99      ( ~ v2_struct_0(sK2) ),
% 3.20/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_41,plain,
% 3.20/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_33,negated_conjecture,
% 3.20/0.99      ( v2_pre_topc(sK2) ),
% 3.20/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_42,plain,
% 3.20/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_32,negated_conjecture,
% 3.20/0.99      ( l1_pre_topc(sK2) ),
% 3.20/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_43,plain,
% 3.20/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_54,plain,
% 3.20/0.99      ( v1_funct_1(sK7) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3707,plain,
% 3.20/0.99      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3756,plain,
% 3.20/0.99      ( v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_3707,c_18]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7005,plain,
% 3.20/0.99      ( v2_pre_topc(X1) != iProver_top
% 3.20/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
% 3.20/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.20/0.99      | m1_pre_topc(sK1,X1) != iProver_top
% 3.20/0.99      | v2_struct_0(X1) = iProver_top
% 3.20/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_6084,c_41,c_42,c_43,c_54,c_3756]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7006,plain,
% 3.20/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
% 3.20/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.20/0.99      | m1_pre_topc(sK1,X1) != iProver_top
% 3.20/0.99      | v2_struct_0(X1) = iProver_top
% 3.20/0.99      | v2_pre_topc(X1) != iProver_top
% 3.20/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_7005]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7017,plain,
% 3.20/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(sK3)) = k3_tmap_1(X0,sK2,sK1,sK3,sK7)
% 3.20/0.99      | m1_pre_topc(sK1,X0) != iProver_top
% 3.20/0.99      | v2_struct_0(X0) = iProver_top
% 3.20/0.99      | v2_pre_topc(X0) != iProver_top
% 3.20/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3697,c_7006]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_12,plain,
% 3.20/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.20/0.99      | ~ m1_pre_topc(X3,X1)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.20/0.99      | v2_struct_0(X1)
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ v2_pre_topc(X1)
% 3.20/0.99      | ~ l1_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X1)
% 3.20/0.99      | ~ v1_funct_1(X0)
% 3.20/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.20/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3713,plain,
% 3.20/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
% 3.20/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.20/0.99      | m1_pre_topc(X3,X0) != iProver_top
% 3.20/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.20/0.99      | v2_struct_0(X1) = iProver_top
% 3.20/0.99      | v2_struct_0(X0) = iProver_top
% 3.20/0.99      | v2_pre_topc(X1) != iProver_top
% 3.20/0.99      | v2_pre_topc(X0) != iProver_top
% 3.20/0.99      | l1_pre_topc(X1) != iProver_top
% 3.20/0.99      | l1_pre_topc(X0) != iProver_top
% 3.20/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5134,plain,
% 3.20/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0)
% 3.20/0.99      | v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 3.20/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.20/0.99      | v2_struct_0(sK1) = iProver_top
% 3.20/0.99      | v2_struct_0(sK2) = iProver_top
% 3.20/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.20/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.20/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.20/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.20/0.99      | v1_funct_1(sK7) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3767,c_3713]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_37,negated_conjecture,
% 3.20/0.99      ( ~ v2_struct_0(sK1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_38,plain,
% 3.20/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_36,negated_conjecture,
% 3.20/0.99      ( v2_pre_topc(sK1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_39,plain,
% 3.20/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_35,negated_conjecture,
% 3.20/0.99      ( l1_pre_topc(sK1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_40,plain,
% 3.20/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5789,plain,
% 3.20/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.20/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_5134,c_38,c_39,c_40,c_41,c_42,c_43,c_54,c_3756]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5790,plain,
% 3.20/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0)
% 3.20/0.99      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_5789]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5797,plain,
% 3.20/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(sK3)) = k2_tmap_1(sK1,sK2,sK7,sK3) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3697,c_5790]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7035,plain,
% 3.20/0.99      ( k3_tmap_1(X0,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3)
% 3.20/0.99      | m1_pre_topc(sK1,X0) != iProver_top
% 3.20/0.99      | v2_struct_0(X0) = iProver_top
% 3.20/0.99      | v2_pre_topc(X0) != iProver_top
% 3.20/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_7017,c_5797]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_8872,plain,
% 3.20/0.99      ( k3_tmap_1(sK1,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3)
% 3.20/0.99      | v2_struct_0(sK1) = iProver_top
% 3.20/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.20/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3747,c_7035]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_8950,plain,
% 3.20/0.99      ( k3_tmap_1(sK1,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_8872,c_38,c_39,c_40]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_16,negated_conjecture,
% 3.20/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
% 3.20/0.99      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
% 3.20/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3709,plain,
% 3.20/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) = iProver_top
% 3.20/0.99      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3810,plain,
% 3.20/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) = iProver_top
% 3.20/0.99      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_3709,c_18]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_8953,plain,
% 3.20/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK7,sK3),sK6) = iProver_top
% 3.20/0.99      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_8950,c_3810]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_10158,plain,
% 3.20/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_10148,c_8953]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_15,negated_conjecture,
% 3.20/0.99      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
% 3.20/0.99      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
% 3.20/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3710,plain,
% 3.20/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) != iProver_top
% 3.20/0.99      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3815,plain,
% 3.20/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) != iProver_top
% 3.20/0.99      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_3710,c_18]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_8954,plain,
% 3.20/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK7,sK3),sK6) != iProver_top
% 3.20/0.99      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_8950,c_3815]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_10159,plain,
% 3.20/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_10148,c_8954]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_10179,plain,
% 3.20/0.99      ( $false ),
% 3.20/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_10158,c_10159]) ).
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  ------                               Statistics
% 3.20/0.99  
% 3.20/0.99  ------ General
% 3.20/0.99  
% 3.20/0.99  abstr_ref_over_cycles:                  0
% 3.20/0.99  abstr_ref_under_cycles:                 0
% 3.20/0.99  gc_basic_clause_elim:                   0
% 3.20/0.99  forced_gc_time:                         0
% 3.20/0.99  parsing_time:                           0.008
% 3.20/0.99  unif_index_cands_time:                  0.
% 3.20/0.99  unif_index_add_time:                    0.
% 3.20/0.99  orderings_time:                         0.
% 3.20/0.99  out_proof_time:                         0.013
% 3.20/0.99  total_time:                             0.279
% 3.20/0.99  num_of_symbols:                         57
% 3.20/0.99  num_of_terms:                           5633
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing
% 3.20/0.99  
% 3.20/0.99  num_of_splits:                          0
% 3.20/0.99  num_of_split_atoms:                     0
% 3.20/0.99  num_of_reused_defs:                     0
% 3.20/0.99  num_eq_ax_congr_red:                    19
% 3.20/0.99  num_of_sem_filtered_clauses:            1
% 3.20/0.99  num_of_subtypes:                        0
% 3.20/0.99  monotx_restored_types:                  0
% 3.20/0.99  sat_num_of_epr_types:                   0
% 3.20/0.99  sat_num_of_non_cyclic_types:            0
% 3.20/0.99  sat_guarded_non_collapsed_types:        0
% 3.20/0.99  num_pure_diseq_elim:                    0
% 3.20/0.99  simp_replaced_by:                       0
% 3.20/0.99  res_preprocessed:                       179
% 3.20/0.99  prep_upred:                             0
% 3.20/0.99  prep_unflattend:                        66
% 3.20/0.99  smt_new_axioms:                         0
% 3.20/0.99  pred_elim_cands:                        11
% 3.20/0.99  pred_elim:                              1
% 3.20/0.99  pred_elim_cl:                           2
% 3.20/0.99  pred_elim_cycles:                       7
% 3.20/0.99  merged_defs:                            16
% 3.20/0.99  merged_defs_ncl:                        0
% 3.20/0.99  bin_hyper_res:                          17
% 3.20/0.99  prep_cycles:                            4
% 3.20/0.99  pred_elim_time:                         0.062
% 3.20/0.99  splitting_time:                         0.
% 3.20/0.99  sem_filter_time:                        0.
% 3.20/0.99  monotx_time:                            0.001
% 3.20/0.99  subtype_inf_time:                       0.
% 3.20/0.99  
% 3.20/0.99  ------ Problem properties
% 3.20/0.99  
% 3.20/0.99  clauses:                                35
% 3.20/0.99  conjectures:                            22
% 3.20/0.99  epr:                                    19
% 3.20/0.99  horn:                                   30
% 3.20/0.99  ground:                                 23
% 3.20/0.99  unary:                                  21
% 3.20/0.99  binary:                                 7
% 3.20/0.99  lits:                                   76
% 3.20/0.99  lits_eq:                                5
% 3.20/0.99  fd_pure:                                0
% 3.20/0.99  fd_pseudo:                              0
% 3.20/0.99  fd_cond:                                0
% 3.20/0.99  fd_pseudo_cond:                         1
% 3.20/0.99  ac_symbols:                             0
% 3.20/0.99  
% 3.20/0.99  ------ Propositional Solver
% 3.20/0.99  
% 3.20/0.99  prop_solver_calls:                      27
% 3.20/0.99  prop_fast_solver_calls:                 2097
% 3.20/0.99  smt_solver_calls:                       0
% 3.20/0.99  smt_fast_solver_calls:                  0
% 3.20/0.99  prop_num_of_clauses:                    2720
% 3.20/0.99  prop_preprocess_simplified:             7755
% 3.20/0.99  prop_fo_subsumed:                       96
% 3.20/0.99  prop_solver_time:                       0.
% 3.20/0.99  smt_solver_time:                        0.
% 3.20/0.99  smt_fast_solver_time:                   0.
% 3.20/0.99  prop_fast_solver_time:                  0.
% 3.20/0.99  prop_unsat_core_time:                   0.
% 3.20/0.99  
% 3.20/0.99  ------ QBF
% 3.20/0.99  
% 3.20/0.99  qbf_q_res:                              0
% 3.20/0.99  qbf_num_tautologies:                    0
% 3.20/0.99  qbf_prep_cycles:                        0
% 3.20/0.99  
% 3.20/0.99  ------ BMC1
% 3.20/0.99  
% 3.20/0.99  bmc1_current_bound:                     -1
% 3.20/0.99  bmc1_last_solved_bound:                 -1
% 3.20/0.99  bmc1_unsat_core_size:                   -1
% 3.20/0.99  bmc1_unsat_core_parents_size:           -1
% 3.20/0.99  bmc1_merge_next_fun:                    0
% 3.20/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.20/0.99  
% 3.20/0.99  ------ Instantiation
% 3.20/0.99  
% 3.20/0.99  inst_num_of_clauses:                    787
% 3.20/0.99  inst_num_in_passive:                    39
% 3.20/0.99  inst_num_in_active:                     428
% 3.20/0.99  inst_num_in_unprocessed:                328
% 3.20/0.99  inst_num_of_loops:                      500
% 3.20/0.99  inst_num_of_learning_restarts:          0
% 3.20/0.99  inst_num_moves_active_passive:          70
% 3.20/0.99  inst_lit_activity:                      0
% 3.20/0.99  inst_lit_activity_moves:                0
% 3.20/0.99  inst_num_tautologies:                   0
% 3.20/0.99  inst_num_prop_implied:                  0
% 3.20/0.99  inst_num_existing_simplified:           0
% 3.20/0.99  inst_num_eq_res_simplified:             0
% 3.20/0.99  inst_num_child_elim:                    0
% 3.20/0.99  inst_num_of_dismatching_blockings:      148
% 3.20/0.99  inst_num_of_non_proper_insts:           714
% 3.20/0.99  inst_num_of_duplicates:                 0
% 3.20/0.99  inst_inst_num_from_inst_to_res:         0
% 3.20/0.99  inst_dismatching_checking_time:         0.
% 3.20/0.99  
% 3.20/0.99  ------ Resolution
% 3.20/0.99  
% 3.20/0.99  res_num_of_clauses:                     0
% 3.20/0.99  res_num_in_passive:                     0
% 3.20/0.99  res_num_in_active:                      0
% 3.20/0.99  res_num_of_loops:                       183
% 3.20/0.99  res_forward_subset_subsumed:            149
% 3.20/0.99  res_backward_subset_subsumed:           16
% 3.20/0.99  res_forward_subsumed:                   0
% 3.20/0.99  res_backward_subsumed:                  0
% 3.20/0.99  res_forward_subsumption_resolution:     7
% 3.20/0.99  res_backward_subsumption_resolution:    0
% 3.20/0.99  res_clause_to_clause_subsumption:       523
% 3.20/0.99  res_orphan_elimination:                 0
% 3.20/0.99  res_tautology_del:                      76
% 3.20/0.99  res_num_eq_res_simplified:              0
% 3.20/0.99  res_num_sel_changes:                    0
% 3.20/0.99  res_moves_from_active_to_pass:          0
% 3.20/0.99  
% 3.20/0.99  ------ Superposition
% 3.20/0.99  
% 3.20/0.99  sup_time_total:                         0.
% 3.20/0.99  sup_time_generating:                    0.
% 3.20/0.99  sup_time_sim_full:                      0.
% 3.20/0.99  sup_time_sim_immed:                     0.
% 3.20/0.99  
% 3.20/0.99  sup_num_of_clauses:                     114
% 3.20/0.99  sup_num_in_active:                      68
% 3.20/0.99  sup_num_in_passive:                     46
% 3.20/0.99  sup_num_of_loops:                       99
% 3.20/0.99  sup_fw_superposition:                   88
% 3.20/0.99  sup_bw_superposition:                   65
% 3.20/0.99  sup_immediate_simplified:               18
% 3.20/0.99  sup_given_eliminated:                   0
% 3.20/0.99  comparisons_done:                       0
% 3.20/0.99  comparisons_avoided:                    0
% 3.20/0.99  
% 3.20/0.99  ------ Simplifications
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  sim_fw_subset_subsumed:                 7
% 3.20/0.99  sim_bw_subset_subsumed:                 15
% 3.20/0.99  sim_fw_subsumed:                        6
% 3.20/0.99  sim_bw_subsumed:                        0
% 3.20/0.99  sim_fw_subsumption_res:                 2
% 3.20/0.99  sim_bw_subsumption_res:                 0
% 3.20/0.99  sim_tautology_del:                      4
% 3.20/0.99  sim_eq_tautology_del:                   3
% 3.20/0.99  sim_eq_res_simp:                        0
% 3.20/0.99  sim_fw_demodulated:                     0
% 3.20/0.99  sim_bw_demodulated:                     23
% 3.20/0.99  sim_light_normalised:                   10
% 3.20/0.99  sim_joinable_taut:                      0
% 3.20/0.99  sim_joinable_simp:                      0
% 3.20/0.99  sim_ac_normalised:                      0
% 3.20/0.99  sim_smt_subsumption:                    0
% 3.20/0.99  
%------------------------------------------------------------------------------
