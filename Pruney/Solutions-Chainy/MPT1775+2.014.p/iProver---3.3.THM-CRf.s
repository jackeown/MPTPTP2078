%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:19 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  238 (1212 expanded)
%              Number of clauses        :  144 ( 252 expanded)
%              Number of leaves         :   22 ( 479 expanded)
%              Depth                    :   30
%              Number of atoms          : 1802 (21045 expanded)
%              Number of equality atoms :  409 (1639 expanded)
%              Maximal formula depth    :   31 (   8 average)
%              Maximal clause size      :   44 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_connsp_2(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X3) )
     => ( r1_tarski(sK0(X0,X1,X2),X2)
        & v3_pre_topc(sK0(X0,X1,X2),X0)
        & m1_connsp_2(sK0(X0,X1,X2),X0,X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK0(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(sK0(X0,X1,X2),X2)
                & v3_pre_topc(sK0(X0,X1,X2),X0)
                & m1_connsp_2(sK0(X0,X1,X2),X0,X1)
                & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(sK0(X0,X1,X2)) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f41])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK0(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK0(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,conjecture,(
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
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
                       => ( ( m1_pre_topc(X2,X3)
                            & v1_tsep_1(X2,X3) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X1,X4,X5)
                                    <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
    inference(flattening,[],[f39])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
    inference(nnf_transformation,[],[f40])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
    inference(flattening,[],[f46])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            | ~ r1_tmap_1(X3,X1,X4,X5) )
          & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            | r1_tmap_1(X3,X1,X4,X5) )
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7)
          | ~ r1_tmap_1(X3,X1,X4,X5) )
        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7)
          | r1_tmap_1(X3,X1,X4,X5) )
        & sK7 = X5
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                | ~ r1_tmap_1(X3,X1,X4,X5) )
              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                | r1_tmap_1(X3,X1,X4,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              | ~ r1_tmap_1(X3,X1,X4,sK6) )
            & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              | r1_tmap_1(X3,X1,X4,sK6) )
            & sK6 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                    | ~ r1_tmap_1(X3,X1,X4,X5) )
                  & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                    | r1_tmap_1(X3,X1,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & m1_pre_topc(X2,X3)
          & v1_tsep_1(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6)
                  | ~ r1_tmap_1(X3,X1,sK5,X5) )
                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6)
                  | r1_tmap_1(X3,X1,sK5,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_pre_topc(X2,X3)
        & v1_tsep_1(X2,X3)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                        | ~ r1_tmap_1(X3,X1,X4,X5) )
                      & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                        | r1_tmap_1(X3,X1,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(X2,X3)
              & v1_tsep_1(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6)
                      | ~ r1_tmap_1(sK4,X1,X4,X5) )
                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6)
                      | r1_tmap_1(sK4,X1,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK4)) )
            & m1_pre_topc(X2,sK4)
            & v1_tsep_1(X2,sK4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,X1,X4,X5) )
                          & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                            | r1_tmap_1(X3,X1,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & v1_tsep_1(X2,X3)
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
                        ( ( ~ r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6)
                          | ~ r1_tmap_1(X3,X1,X4,X5) )
                        & ( r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6)
                          | r1_tmap_1(X3,X1,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK3)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(sK3,X3)
                & v1_tsep_1(sK3,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
                            ( ( ~ r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,sK2,X4,X5) )
                            & ( r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6)
                              | r1_tmap_1(X3,sK2,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & v1_tsep_1(X2,X3)
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

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | r1_tmap_1(X3,X1,X4,X5) )
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & v1_tsep_1(X2,X3)
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
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
    ( ( ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)
      | ~ r1_tmap_1(sK4,sK2,sK5,sK6) )
    & ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)
      | r1_tmap_1(sK4,sK2,sK5,sK6) )
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK3))
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_pre_topc(sK3,sK4)
    & v1_tsep_1(sK3,sK4)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f47,f54,f53,f52,f51,f50,f49,f48])).

fof(f94,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)
    | r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f93,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f55])).

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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f100,plain,(
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
    inference(equality_resolution,[],[f75])).

fof(f87,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f76,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f77,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f78,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f82,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f55])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f101,plain,(
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
    inference(equality_resolution,[],[f74])).

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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f35])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f36])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f73])).

fof(f95,plain,
    ( ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)
    | ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f89,plain,(
    v1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_7,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_5,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_260,plain,
    ( r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_5])).

cnf(c_261,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_260])).

cnf(c_1560,plain,
    ( ~ m1_connsp_2(X0_56,X0_55,X1_56)
    | r1_tarski(sK0(X0_55,X1_56,X0_56),X0_56)
    | ~ m1_subset_1(X1_56,u1_struct_0(X0_55))
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55)
    | ~ v2_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_261])).

cnf(c_2376,plain,
    ( m1_connsp_2(X0_56,X0_55,X1_56) != iProver_top
    | r1_tarski(sK0(X0_55,X1_56,X0_56),X0_56) = iProver_top
    | m1_subset_1(X1_56,u1_struct_0(X0_55)) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1560])).

cnf(c_9,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_246,plain,
    ( m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_5])).

cnf(c_247,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_246])).

cnf(c_1562,plain,
    ( ~ m1_connsp_2(X0_56,X0_55,X1_56)
    | m1_connsp_2(sK0(X0_55,X1_56,X0_56),X0_55,X1_56)
    | ~ m1_subset_1(X1_56,u1_struct_0(X0_55))
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55)
    | ~ v2_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_247])).

cnf(c_2374,plain,
    ( m1_connsp_2(X0_56,X0_55,X1_56) != iProver_top
    | m1_connsp_2(sK0(X0_55,X1_56,X0_56),X0_55,X1_56) = iProver_top
    | m1_subset_1(X1_56,u1_struct_0(X0_55)) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1562])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_239,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_5])).

cnf(c_1563,plain,
    ( ~ m1_connsp_2(X0_56,X0_55,X1_56)
    | ~ m1_subset_1(X1_56,u1_struct_0(X0_55))
    | m1_subset_1(sK0(X0_55,X1_56,X0_56),k1_zfmisc_1(u1_struct_0(X0_55)))
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55)
    | ~ v2_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_239])).

cnf(c_2373,plain,
    ( m1_connsp_2(X0_56,X0_55,X1_56) != iProver_top
    | m1_subset_1(X1_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK0(X0_55,X1_56,X0_56),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1563])).

cnf(c_21,negated_conjecture,
    ( r1_tmap_1(sK4,sK2,sK5,sK6)
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1580,negated_conjecture,
    ( r1_tmap_1(sK4,sK2,sK5,sK6)
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2357,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK6) = iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1580])).

cnf(c_22,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1579,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2436,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2357,c_1579])).

cnf(c_18,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_867,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_868,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_867])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_872,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_connsp_2(X5,X3,X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_868,c_29])).

cnf(c_873,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_872])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_920,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_873,c_16])).

cnf(c_1556,plain,
    ( ~ r1_tmap_1(X0_55,X1_55,k3_tmap_1(X2_55,X1_55,X3_55,X0_55,sK5),X0_56)
    | r1_tmap_1(X3_55,X1_55,sK5,X0_56)
    | ~ m1_connsp_2(X1_56,X3_55,X0_56)
    | ~ r1_tarski(X1_56,u1_struct_0(X0_55))
    | ~ m1_pre_topc(X3_55,X2_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X3_55)))
    | ~ m1_subset_1(X0_56,u1_struct_0(X3_55))
    | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_55),u1_struct_0(X1_55))))
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | v2_struct_0(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X2_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X2_55)
    | u1_struct_0(X3_55) != u1_struct_0(sK4)
    | u1_struct_0(X1_55) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_920])).

cnf(c_2380,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK4)
    | u1_struct_0(X1_55) != u1_struct_0(sK2)
    | r1_tmap_1(X2_55,X1_55,k3_tmap_1(X3_55,X1_55,X0_55,X2_55,sK5),X0_56) != iProver_top
    | r1_tmap_1(X0_55,X1_55,sK5,X0_56) = iProver_top
    | m1_connsp_2(X1_56,X0_55,X0_56) != iProver_top
    | r1_tarski(X1_56,u1_struct_0(X2_55)) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X2_55)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1556])).

cnf(c_3609,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK4)
    | r1_tmap_1(X1_55,sK2,k3_tmap_1(X2_55,sK2,X0_55,X1_55,sK5),X0_56) != iProver_top
    | r1_tmap_1(X0_55,sK2,sK5,X0_56) = iProver_top
    | m1_connsp_2(X1_56,X0_55,X0_56) != iProver_top
    | r1_tarski(X1_56,u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2380])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_43,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_44,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_45,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3687,plain,
    ( v2_pre_topc(X2_55) != iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | r1_tarski(X1_56,u1_struct_0(X1_55)) != iProver_top
    | m1_connsp_2(X1_56,X0_55,X0_56) != iProver_top
    | r1_tmap_1(X0_55,sK2,sK5,X0_56) = iProver_top
    | r1_tmap_1(X1_55,sK2,k3_tmap_1(X2_55,sK2,X0_55,X1_55,sK5),X0_56) != iProver_top
    | u1_struct_0(X0_55) != u1_struct_0(sK4)
    | l1_pre_topc(X2_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3609,c_43,c_44,c_45])).

cnf(c_3688,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK4)
    | r1_tmap_1(X1_55,sK2,k3_tmap_1(X2_55,sK2,X0_55,X1_55,sK5),X0_56) != iProver_top
    | r1_tmap_1(X0_55,sK2,sK5,X0_56) = iProver_top
    | m1_connsp_2(X1_56,X0_55,X0_56) != iProver_top
    | r1_tarski(X1_56,u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_3687])).

cnf(c_3707,plain,
    ( r1_tmap_1(X0_55,sK2,k3_tmap_1(X1_55,sK2,sK4,X0_55,sK5),X0_56) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X0_56) = iProver_top
    | m1_connsp_2(X1_56,sK4,X0_56) != iProver_top
    | r1_tarski(X1_56,u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(X0_55,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_55) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3688])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_48,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_52,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3824,plain,
    ( v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | r1_tmap_1(X0_55,sK2,k3_tmap_1(X1_55,sK2,sK4,X0_55,sK5),X0_56) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X0_56) = iProver_top
    | m1_connsp_2(X1_56,sK4,X0_56) != iProver_top
    | r1_tarski(X1_56,u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(X0_55,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_55) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3707,c_48,c_52])).

cnf(c_3825,plain,
    ( r1_tmap_1(X0_55,sK2,k3_tmap_1(X1_55,sK2,sK4,X0_55,sK5),X0_56) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X0_56) = iProver_top
    | m1_connsp_2(X1_56,sK4,X0_56) != iProver_top
    | r1_tarski(X1_56,u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(X0_55,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_55) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_3824])).

cnf(c_3843,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
    | m1_connsp_2(X0_56,sK4,sK7) != iProver_top
    | r1_tarski(X0_56,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2436,c_3825])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_40,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_41,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_42,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_46,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_49,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_54,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_56,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1577,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_2359,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1577])).

cnf(c_2407,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2359,c_1579])).

cnf(c_19,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_17,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_209,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_17])).

cnf(c_210,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(renaming,[status(thm)],[c_209])).

cnf(c_801,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_210,c_28])).

cnf(c_802,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_801])).

cnf(c_806,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_802,c_29])).

cnf(c_807,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_806])).

cnf(c_848,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_807,c_16])).

cnf(c_1557,plain,
    ( r1_tmap_1(X0_55,X1_55,k3_tmap_1(X2_55,X1_55,X3_55,X0_55,sK5),X0_56)
    | ~ r1_tmap_1(X3_55,X1_55,sK5,X0_56)
    | ~ m1_pre_topc(X3_55,X2_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_56,u1_struct_0(X3_55))
    | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_55),u1_struct_0(X1_55))))
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | v2_struct_0(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X2_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X2_55)
    | u1_struct_0(X3_55) != u1_struct_0(sK4)
    | u1_struct_0(X1_55) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_848])).

cnf(c_2379,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK4)
    | u1_struct_0(X1_55) != u1_struct_0(sK2)
    | r1_tmap_1(X2_55,X1_55,k3_tmap_1(X3_55,X1_55,X0_55,X2_55,sK5),X0_56) = iProver_top
    | r1_tmap_1(X0_55,X1_55,sK5,X0_56) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X2_55)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1557])).

cnf(c_3584,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK4)
    | r1_tmap_1(X1_55,sK2,k3_tmap_1(X2_55,sK2,X0_55,X1_55,sK5),X0_56) = iProver_top
    | r1_tmap_1(X0_55,sK2,sK5,X0_56) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2379])).

cnf(c_3665,plain,
    ( v2_pre_topc(X2_55) != iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | r1_tmap_1(X0_55,sK2,sK5,X0_56) != iProver_top
    | r1_tmap_1(X1_55,sK2,k3_tmap_1(X2_55,sK2,X0_55,X1_55,sK5),X0_56) = iProver_top
    | u1_struct_0(X0_55) != u1_struct_0(sK4)
    | l1_pre_topc(X2_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3584,c_43,c_44,c_45])).

cnf(c_3666,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK4)
    | r1_tmap_1(X1_55,sK2,k3_tmap_1(X2_55,sK2,X0_55,X1_55,sK5),X0_56) = iProver_top
    | r1_tmap_1(X0_55,sK2,sK5,X0_56) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_3665])).

cnf(c_3682,plain,
    ( r1_tmap_1(X0_55,sK2,k3_tmap_1(X1_55,sK2,sK4,X0_55,sK5),X0_56) = iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X0_56) != iProver_top
    | m1_pre_topc(X0_55,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_55) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3666])).

cnf(c_3753,plain,
    ( v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | r1_tmap_1(X0_55,sK2,k3_tmap_1(X1_55,sK2,sK4,X0_55,sK5),X0_56) = iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X0_56) != iProver_top
    | m1_pre_topc(X0_55,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_55) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3682,c_48,c_52])).

cnf(c_3754,plain,
    ( r1_tmap_1(X0_55,sK2,k3_tmap_1(X1_55,sK2,sK4,X0_55,sK5),X0_56) = iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X0_56) != iProver_top
    | m1_pre_topc(X0_55,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_55) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_3753])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK6)
    | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1581,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK6)
    | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2356,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK6) != iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1581])).

cnf(c_2447,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2356,c_1579])).

cnf(c_3769,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3754,c_2447])).

cnf(c_3873,plain,
    ( m1_connsp_2(X0_56,sK4,sK7) != iProver_top
    | r1_tarski(X0_56,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3843,c_40,c_41,c_42,c_46,c_49,c_54,c_56,c_2407,c_3769])).

cnf(c_4068,plain,
    ( m1_connsp_2(X0_56,sK4,X1_56) != iProver_top
    | m1_connsp_2(sK0(sK4,X1_56,X0_56),sK4,sK7) != iProver_top
    | r1_tarski(sK0(sK4,X1_56,X0_56),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2373,c_3873])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1586,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2720,plain,
    ( ~ m1_pre_topc(sK4,X0_55)
    | ~ l1_pre_topc(X0_55)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1586])).

cnf(c_3013,plain,
    ( ~ m1_pre_topc(sK4,sK1)
    | l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2720])).

cnf(c_3014,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3013])).

cnf(c_1574,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_2362,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1574])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1587,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v2_pre_topc(X1_55)
    | v2_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2350,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1587])).

cnf(c_3108,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2362,c_2350])).

cnf(c_4185,plain,
    ( m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK0(sK4,X1_56,X0_56),u1_struct_0(sK3)) != iProver_top
    | m1_connsp_2(sK0(sK4,X1_56,X0_56),sK4,sK7) != iProver_top
    | m1_connsp_2(X0_56,sK4,X1_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4068,c_41,c_42,c_48,c_49,c_3014,c_3108])).

cnf(c_4186,plain,
    ( m1_connsp_2(X0_56,sK4,X1_56) != iProver_top
    | m1_connsp_2(sK0(sK4,X1_56,X0_56),sK4,sK7) != iProver_top
    | r1_tarski(sK0(sK4,X1_56,X0_56),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4185])).

cnf(c_4364,plain,
    ( m1_connsp_2(X0_56,sK4,sK7) != iProver_top
    | r1_tarski(sK0(sK4,sK7,X0_56),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2374,c_4186])).

cnf(c_4381,plain,
    ( m1_connsp_2(X0_56,sK4,sK7) != iProver_top
    | r1_tarski(sK0(sK4,sK7,X0_56),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4364,c_41,c_42,c_48,c_49,c_2407,c_3014,c_3108])).

cnf(c_4389,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK4,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2376,c_4381])).

cnf(c_6,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1584,plain,
    ( m1_connsp_2(X0_56,X0_55,X1_56)
    | ~ v3_pre_topc(X0_56,X0_55)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ m1_subset_1(X1_56,u1_struct_0(X0_55))
    | ~ r2_hidden(X1_56,X0_56)
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55)
    | ~ v2_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3415,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK4,X0_56)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK4)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0_56,u1_struct_0(sK3))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1584])).

cnf(c_4017,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK4,sK7)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK4)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r2_hidden(sK7,u1_struct_0(sK3))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_3415])).

cnf(c_4021,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK4,sK7) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),sK4) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK7,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4017])).

cnf(c_1576,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2360,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1576])).

cnf(c_2351,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1586])).

cnf(c_3135,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_2351])).

cnf(c_14,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_218,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_15])).

cnf(c_219,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_218])).

cnf(c_26,negated_conjecture,
    ( v1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_645,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_219,c_26])).

cnf(c_646,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK4)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_645])).

cnf(c_648,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_646,c_25])).

cnf(c_1558,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subtyping,[status(esa)],[c_648])).

cnf(c_2378,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1558])).

cnf(c_647,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK4) = iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_646])).

cnf(c_3073,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2378,c_42,c_49,c_54,c_647,c_3014])).

cnf(c_1578,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2358,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1578])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1588,plain,
    ( ~ m1_subset_1(X0_56,X1_56)
    | r2_hidden(X0_56,X1_56)
    | v1_xboole_0(X1_56) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2349,plain,
    ( m1_subset_1(X0_56,X1_56) != iProver_top
    | r2_hidden(X0_56,X1_56) = iProver_top
    | v1_xboole_0(X1_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1588])).

cnf(c_2989,plain,
    ( r2_hidden(sK7,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2358,c_2349])).

cnf(c_2,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_528,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_2,c_4])).

cnf(c_1559,plain,
    ( v2_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55)
    | ~ v1_xboole_0(u1_struct_0(X0_55)) ),
    inference(subtyping,[status(esa)],[c_528])).

cnf(c_2865,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1559])).

cnf(c_2866,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2865])).

cnf(c_1583,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2727,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1583])).

cnf(c_2728,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2727])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4389,c_4021,c_3135,c_3108,c_3073,c_3014,c_2989,c_2866,c_2728,c_2407,c_54,c_49,c_48,c_46,c_42,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.21/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/0.95  
% 2.21/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.21/0.95  
% 2.21/0.95  ------  iProver source info
% 2.21/0.95  
% 2.21/0.95  git: date: 2020-06-30 10:37:57 +0100
% 2.21/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.21/0.95  git: non_committed_changes: false
% 2.21/0.95  git: last_make_outside_of_git: false
% 2.21/0.95  
% 2.21/0.95  ------ 
% 2.21/0.95  
% 2.21/0.95  ------ Input Options
% 2.21/0.95  
% 2.21/0.95  --out_options                           all
% 2.21/0.95  --tptp_safe_out                         true
% 2.21/0.95  --problem_path                          ""
% 2.21/0.95  --include_path                          ""
% 2.21/0.95  --clausifier                            res/vclausify_rel
% 2.21/0.95  --clausifier_options                    --mode clausify
% 2.21/0.95  --stdin                                 false
% 2.21/0.95  --stats_out                             all
% 2.21/0.95  
% 2.21/0.95  ------ General Options
% 2.21/0.95  
% 2.21/0.95  --fof                                   false
% 2.21/0.95  --time_out_real                         305.
% 2.21/0.95  --time_out_virtual                      -1.
% 2.21/0.95  --symbol_type_check                     false
% 2.21/0.95  --clausify_out                          false
% 2.21/0.95  --sig_cnt_out                           false
% 2.21/0.95  --trig_cnt_out                          false
% 2.21/0.95  --trig_cnt_out_tolerance                1.
% 2.21/0.95  --trig_cnt_out_sk_spl                   false
% 2.21/0.95  --abstr_cl_out                          false
% 2.21/0.95  
% 2.21/0.95  ------ Global Options
% 2.21/0.95  
% 2.21/0.95  --schedule                              default
% 2.21/0.95  --add_important_lit                     false
% 2.21/0.95  --prop_solver_per_cl                    1000
% 2.21/0.95  --min_unsat_core                        false
% 2.21/0.95  --soft_assumptions                      false
% 2.21/0.95  --soft_lemma_size                       3
% 2.21/0.95  --prop_impl_unit_size                   0
% 2.21/0.95  --prop_impl_unit                        []
% 2.21/0.95  --share_sel_clauses                     true
% 2.21/0.95  --reset_solvers                         false
% 2.21/0.95  --bc_imp_inh                            [conj_cone]
% 2.21/0.95  --conj_cone_tolerance                   3.
% 2.21/0.95  --extra_neg_conj                        none
% 2.21/0.95  --large_theory_mode                     true
% 2.21/0.95  --prolific_symb_bound                   200
% 2.21/0.95  --lt_threshold                          2000
% 2.21/0.95  --clause_weak_htbl                      true
% 2.21/0.95  --gc_record_bc_elim                     false
% 2.21/0.95  
% 2.21/0.95  ------ Preprocessing Options
% 2.21/0.95  
% 2.21/0.95  --preprocessing_flag                    true
% 2.21/0.95  --time_out_prep_mult                    0.1
% 2.21/0.95  --splitting_mode                        input
% 2.21/0.95  --splitting_grd                         true
% 2.21/0.95  --splitting_cvd                         false
% 2.21/0.95  --splitting_cvd_svl                     false
% 2.21/0.95  --splitting_nvd                         32
% 2.21/0.95  --sub_typing                            true
% 2.21/0.95  --prep_gs_sim                           true
% 2.21/0.95  --prep_unflatten                        true
% 2.21/0.95  --prep_res_sim                          true
% 2.21/0.95  --prep_upred                            true
% 2.21/0.95  --prep_sem_filter                       exhaustive
% 2.21/0.95  --prep_sem_filter_out                   false
% 2.21/0.95  --pred_elim                             true
% 2.21/0.95  --res_sim_input                         true
% 2.21/0.95  --eq_ax_congr_red                       true
% 2.21/0.95  --pure_diseq_elim                       true
% 2.21/0.95  --brand_transform                       false
% 2.21/0.95  --non_eq_to_eq                          false
% 2.21/0.95  --prep_def_merge                        true
% 2.21/0.95  --prep_def_merge_prop_impl              false
% 2.21/0.95  --prep_def_merge_mbd                    true
% 2.21/0.95  --prep_def_merge_tr_red                 false
% 2.21/0.95  --prep_def_merge_tr_cl                  false
% 2.21/0.95  --smt_preprocessing                     true
% 2.21/0.95  --smt_ac_axioms                         fast
% 2.21/0.95  --preprocessed_out                      false
% 2.21/0.95  --preprocessed_stats                    false
% 2.21/0.95  
% 2.21/0.95  ------ Abstraction refinement Options
% 2.21/0.95  
% 2.21/0.95  --abstr_ref                             []
% 2.21/0.95  --abstr_ref_prep                        false
% 2.21/0.95  --abstr_ref_until_sat                   false
% 2.21/0.95  --abstr_ref_sig_restrict                funpre
% 2.21/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/0.95  --abstr_ref_under                       []
% 2.21/0.95  
% 2.21/0.95  ------ SAT Options
% 2.21/0.95  
% 2.21/0.95  --sat_mode                              false
% 2.21/0.95  --sat_fm_restart_options                ""
% 2.21/0.95  --sat_gr_def                            false
% 2.21/0.95  --sat_epr_types                         true
% 2.21/0.95  --sat_non_cyclic_types                  false
% 2.21/0.95  --sat_finite_models                     false
% 2.21/0.95  --sat_fm_lemmas                         false
% 2.21/0.95  --sat_fm_prep                           false
% 2.21/0.95  --sat_fm_uc_incr                        true
% 2.21/0.95  --sat_out_model                         small
% 2.21/0.95  --sat_out_clauses                       false
% 2.21/0.95  
% 2.21/0.95  ------ QBF Options
% 2.21/0.95  
% 2.21/0.95  --qbf_mode                              false
% 2.21/0.95  --qbf_elim_univ                         false
% 2.21/0.95  --qbf_dom_inst                          none
% 2.21/0.95  --qbf_dom_pre_inst                      false
% 2.21/0.95  --qbf_sk_in                             false
% 2.21/0.95  --qbf_pred_elim                         true
% 2.21/0.95  --qbf_split                             512
% 2.21/0.95  
% 2.21/0.95  ------ BMC1 Options
% 2.21/0.95  
% 2.21/0.95  --bmc1_incremental                      false
% 2.21/0.95  --bmc1_axioms                           reachable_all
% 2.21/0.95  --bmc1_min_bound                        0
% 2.21/0.95  --bmc1_max_bound                        -1
% 2.21/0.95  --bmc1_max_bound_default                -1
% 2.21/0.95  --bmc1_symbol_reachability              true
% 2.21/0.95  --bmc1_property_lemmas                  false
% 2.21/0.95  --bmc1_k_induction                      false
% 2.21/0.95  --bmc1_non_equiv_states                 false
% 2.21/0.95  --bmc1_deadlock                         false
% 2.21/0.95  --bmc1_ucm                              false
% 2.21/0.95  --bmc1_add_unsat_core                   none
% 2.21/0.95  --bmc1_unsat_core_children              false
% 2.21/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/0.95  --bmc1_out_stat                         full
% 2.21/0.95  --bmc1_ground_init                      false
% 2.21/0.95  --bmc1_pre_inst_next_state              false
% 2.21/0.95  --bmc1_pre_inst_state                   false
% 2.21/0.95  --bmc1_pre_inst_reach_state             false
% 2.21/0.95  --bmc1_out_unsat_core                   false
% 2.21/0.95  --bmc1_aig_witness_out                  false
% 2.21/0.95  --bmc1_verbose                          false
% 2.21/0.95  --bmc1_dump_clauses_tptp                false
% 2.21/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.21/0.95  --bmc1_dump_file                        -
% 2.21/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.21/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.21/0.95  --bmc1_ucm_extend_mode                  1
% 2.21/0.95  --bmc1_ucm_init_mode                    2
% 2.21/0.95  --bmc1_ucm_cone_mode                    none
% 2.21/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.21/0.95  --bmc1_ucm_relax_model                  4
% 2.21/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.21/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/0.95  --bmc1_ucm_layered_model                none
% 2.21/0.95  --bmc1_ucm_max_lemma_size               10
% 2.21/0.95  
% 2.21/0.95  ------ AIG Options
% 2.21/0.95  
% 2.21/0.95  --aig_mode                              false
% 2.21/0.95  
% 2.21/0.95  ------ Instantiation Options
% 2.21/0.95  
% 2.21/0.95  --instantiation_flag                    true
% 2.21/0.95  --inst_sos_flag                         false
% 2.21/0.95  --inst_sos_phase                        true
% 2.21/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/0.95  --inst_lit_sel_side                     num_symb
% 2.21/0.95  --inst_solver_per_active                1400
% 2.21/0.95  --inst_solver_calls_frac                1.
% 2.21/0.95  --inst_passive_queue_type               priority_queues
% 2.21/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/0.95  --inst_passive_queues_freq              [25;2]
% 2.21/0.95  --inst_dismatching                      true
% 2.21/0.95  --inst_eager_unprocessed_to_passive     true
% 2.21/0.95  --inst_prop_sim_given                   true
% 2.21/0.95  --inst_prop_sim_new                     false
% 2.21/0.95  --inst_subs_new                         false
% 2.21/0.95  --inst_eq_res_simp                      false
% 2.21/0.95  --inst_subs_given                       false
% 2.21/0.95  --inst_orphan_elimination               true
% 2.21/0.95  --inst_learning_loop_flag               true
% 2.21/0.95  --inst_learning_start                   3000
% 2.21/0.95  --inst_learning_factor                  2
% 2.21/0.95  --inst_start_prop_sim_after_learn       3
% 2.21/0.95  --inst_sel_renew                        solver
% 2.21/0.95  --inst_lit_activity_flag                true
% 2.21/0.95  --inst_restr_to_given                   false
% 2.21/0.95  --inst_activity_threshold               500
% 2.21/0.95  --inst_out_proof                        true
% 2.21/0.95  
% 2.21/0.95  ------ Resolution Options
% 2.21/0.95  
% 2.21/0.95  --resolution_flag                       true
% 2.21/0.95  --res_lit_sel                           adaptive
% 2.21/0.95  --res_lit_sel_side                      none
% 2.21/0.95  --res_ordering                          kbo
% 2.21/0.95  --res_to_prop_solver                    active
% 2.21/0.95  --res_prop_simpl_new                    false
% 2.21/0.95  --res_prop_simpl_given                  true
% 2.21/0.95  --res_passive_queue_type                priority_queues
% 2.21/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/0.95  --res_passive_queues_freq               [15;5]
% 2.21/0.95  --res_forward_subs                      full
% 2.21/0.95  --res_backward_subs                     full
% 2.21/0.95  --res_forward_subs_resolution           true
% 2.21/0.95  --res_backward_subs_resolution          true
% 2.21/0.95  --res_orphan_elimination                true
% 2.21/0.95  --res_time_limit                        2.
% 2.21/0.95  --res_out_proof                         true
% 2.21/0.95  
% 2.21/0.95  ------ Superposition Options
% 2.21/0.95  
% 2.21/0.95  --superposition_flag                    true
% 2.21/0.95  --sup_passive_queue_type                priority_queues
% 2.21/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.21/0.95  --demod_completeness_check              fast
% 2.21/0.95  --demod_use_ground                      true
% 2.21/0.95  --sup_to_prop_solver                    passive
% 2.21/0.95  --sup_prop_simpl_new                    true
% 2.21/0.95  --sup_prop_simpl_given                  true
% 2.21/0.95  --sup_fun_splitting                     false
% 2.21/0.95  --sup_smt_interval                      50000
% 2.21/0.95  
% 2.21/0.95  ------ Superposition Simplification Setup
% 2.21/0.95  
% 2.21/0.95  --sup_indices_passive                   []
% 2.21/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.95  --sup_full_bw                           [BwDemod]
% 2.21/0.95  --sup_immed_triv                        [TrivRules]
% 2.21/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.95  --sup_immed_bw_main                     []
% 2.21/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/0.95  
% 2.21/0.95  ------ Combination Options
% 2.21/0.95  
% 2.21/0.95  --comb_res_mult                         3
% 2.21/0.95  --comb_sup_mult                         2
% 2.21/0.95  --comb_inst_mult                        10
% 2.21/0.95  
% 2.21/0.95  ------ Debug Options
% 2.21/0.95  
% 2.21/0.95  --dbg_backtrace                         false
% 2.21/0.95  --dbg_dump_prop_clauses                 false
% 2.21/0.95  --dbg_dump_prop_clauses_file            -
% 2.21/0.95  --dbg_out_stat                          false
% 2.21/0.95  ------ Parsing...
% 2.21/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.21/0.95  
% 2.21/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.21/0.95  
% 2.21/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.21/0.95  
% 2.21/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.21/0.95  ------ Proving...
% 2.21/0.95  ------ Problem Properties 
% 2.21/0.95  
% 2.21/0.95  
% 2.21/0.95  clauses                                 33
% 2.21/0.95  conjectures                             17
% 2.21/0.95  EPR                                     16
% 2.21/0.95  Horn                                    23
% 2.21/0.95  unary                                   15
% 2.21/0.95  binary                                  2
% 2.21/0.95  lits                                    124
% 2.21/0.95  lits eq                                 5
% 2.21/0.95  fd_pure                                 0
% 2.21/0.95  fd_pseudo                               0
% 2.21/0.95  fd_cond                                 0
% 2.21/0.95  fd_pseudo_cond                          0
% 2.21/0.95  AC symbols                              0
% 2.21/0.95  
% 2.21/0.95  ------ Schedule dynamic 5 is on 
% 2.21/0.95  
% 2.21/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.21/0.95  
% 2.21/0.95  
% 2.21/0.95  ------ 
% 2.21/0.95  Current options:
% 2.21/0.95  ------ 
% 2.21/0.95  
% 2.21/0.95  ------ Input Options
% 2.21/0.95  
% 2.21/0.95  --out_options                           all
% 2.21/0.95  --tptp_safe_out                         true
% 2.21/0.95  --problem_path                          ""
% 2.21/0.95  --include_path                          ""
% 2.21/0.95  --clausifier                            res/vclausify_rel
% 2.21/0.95  --clausifier_options                    --mode clausify
% 2.21/0.95  --stdin                                 false
% 2.21/0.95  --stats_out                             all
% 2.21/0.95  
% 2.21/0.95  ------ General Options
% 2.21/0.95  
% 2.21/0.95  --fof                                   false
% 2.21/0.95  --time_out_real                         305.
% 2.21/0.95  --time_out_virtual                      -1.
% 2.21/0.95  --symbol_type_check                     false
% 2.21/0.95  --clausify_out                          false
% 2.21/0.95  --sig_cnt_out                           false
% 2.21/0.95  --trig_cnt_out                          false
% 2.21/0.95  --trig_cnt_out_tolerance                1.
% 2.21/0.95  --trig_cnt_out_sk_spl                   false
% 2.21/0.95  --abstr_cl_out                          false
% 2.21/0.95  
% 2.21/0.95  ------ Global Options
% 2.21/0.95  
% 2.21/0.95  --schedule                              default
% 2.21/0.95  --add_important_lit                     false
% 2.21/0.95  --prop_solver_per_cl                    1000
% 2.21/0.95  --min_unsat_core                        false
% 2.21/0.95  --soft_assumptions                      false
% 2.21/0.95  --soft_lemma_size                       3
% 2.21/0.95  --prop_impl_unit_size                   0
% 2.21/0.95  --prop_impl_unit                        []
% 2.21/0.95  --share_sel_clauses                     true
% 2.21/0.95  --reset_solvers                         false
% 2.21/0.95  --bc_imp_inh                            [conj_cone]
% 2.21/0.95  --conj_cone_tolerance                   3.
% 2.21/0.95  --extra_neg_conj                        none
% 2.21/0.95  --large_theory_mode                     true
% 2.21/0.95  --prolific_symb_bound                   200
% 2.21/0.95  --lt_threshold                          2000
% 2.21/0.95  --clause_weak_htbl                      true
% 2.21/0.95  --gc_record_bc_elim                     false
% 2.21/0.95  
% 2.21/0.95  ------ Preprocessing Options
% 2.21/0.95  
% 2.21/0.95  --preprocessing_flag                    true
% 2.21/0.95  --time_out_prep_mult                    0.1
% 2.21/0.95  --splitting_mode                        input
% 2.21/0.95  --splitting_grd                         true
% 2.21/0.95  --splitting_cvd                         false
% 2.21/0.95  --splitting_cvd_svl                     false
% 2.21/0.95  --splitting_nvd                         32
% 2.21/0.95  --sub_typing                            true
% 2.21/0.95  --prep_gs_sim                           true
% 2.21/0.95  --prep_unflatten                        true
% 2.21/0.95  --prep_res_sim                          true
% 2.21/0.95  --prep_upred                            true
% 2.21/0.95  --prep_sem_filter                       exhaustive
% 2.21/0.95  --prep_sem_filter_out                   false
% 2.21/0.95  --pred_elim                             true
% 2.21/0.95  --res_sim_input                         true
% 2.21/0.95  --eq_ax_congr_red                       true
% 2.21/0.95  --pure_diseq_elim                       true
% 2.21/0.95  --brand_transform                       false
% 2.21/0.95  --non_eq_to_eq                          false
% 2.21/0.95  --prep_def_merge                        true
% 2.21/0.95  --prep_def_merge_prop_impl              false
% 2.21/0.95  --prep_def_merge_mbd                    true
% 2.21/0.95  --prep_def_merge_tr_red                 false
% 2.21/0.95  --prep_def_merge_tr_cl                  false
% 2.21/0.95  --smt_preprocessing                     true
% 2.21/0.95  --smt_ac_axioms                         fast
% 2.21/0.95  --preprocessed_out                      false
% 2.21/0.95  --preprocessed_stats                    false
% 2.21/0.95  
% 2.21/0.95  ------ Abstraction refinement Options
% 2.21/0.95  
% 2.21/0.95  --abstr_ref                             []
% 2.21/0.95  --abstr_ref_prep                        false
% 2.21/0.95  --abstr_ref_until_sat                   false
% 2.21/0.95  --abstr_ref_sig_restrict                funpre
% 2.21/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/0.95  --abstr_ref_under                       []
% 2.21/0.95  
% 2.21/0.95  ------ SAT Options
% 2.21/0.95  
% 2.21/0.95  --sat_mode                              false
% 2.21/0.95  --sat_fm_restart_options                ""
% 2.21/0.95  --sat_gr_def                            false
% 2.21/0.95  --sat_epr_types                         true
% 2.21/0.95  --sat_non_cyclic_types                  false
% 2.21/0.95  --sat_finite_models                     false
% 2.21/0.95  --sat_fm_lemmas                         false
% 2.21/0.95  --sat_fm_prep                           false
% 2.21/0.95  --sat_fm_uc_incr                        true
% 2.21/0.95  --sat_out_model                         small
% 2.21/0.95  --sat_out_clauses                       false
% 2.21/0.95  
% 2.21/0.95  ------ QBF Options
% 2.21/0.95  
% 2.21/0.95  --qbf_mode                              false
% 2.21/0.95  --qbf_elim_univ                         false
% 2.21/0.95  --qbf_dom_inst                          none
% 2.21/0.95  --qbf_dom_pre_inst                      false
% 2.21/0.95  --qbf_sk_in                             false
% 2.21/0.95  --qbf_pred_elim                         true
% 2.21/0.95  --qbf_split                             512
% 2.21/0.95  
% 2.21/0.95  ------ BMC1 Options
% 2.21/0.95  
% 2.21/0.95  --bmc1_incremental                      false
% 2.21/0.95  --bmc1_axioms                           reachable_all
% 2.21/0.95  --bmc1_min_bound                        0
% 2.21/0.95  --bmc1_max_bound                        -1
% 2.21/0.95  --bmc1_max_bound_default                -1
% 2.21/0.95  --bmc1_symbol_reachability              true
% 2.21/0.95  --bmc1_property_lemmas                  false
% 2.21/0.95  --bmc1_k_induction                      false
% 2.21/0.95  --bmc1_non_equiv_states                 false
% 2.21/0.95  --bmc1_deadlock                         false
% 2.21/0.95  --bmc1_ucm                              false
% 2.21/0.95  --bmc1_add_unsat_core                   none
% 2.21/0.95  --bmc1_unsat_core_children              false
% 2.21/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/0.95  --bmc1_out_stat                         full
% 2.21/0.95  --bmc1_ground_init                      false
% 2.21/0.95  --bmc1_pre_inst_next_state              false
% 2.21/0.95  --bmc1_pre_inst_state                   false
% 2.21/0.95  --bmc1_pre_inst_reach_state             false
% 2.21/0.95  --bmc1_out_unsat_core                   false
% 2.21/0.95  --bmc1_aig_witness_out                  false
% 2.21/0.95  --bmc1_verbose                          false
% 2.21/0.95  --bmc1_dump_clauses_tptp                false
% 2.21/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.21/0.95  --bmc1_dump_file                        -
% 2.21/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.21/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.21/0.95  --bmc1_ucm_extend_mode                  1
% 2.21/0.95  --bmc1_ucm_init_mode                    2
% 2.21/0.95  --bmc1_ucm_cone_mode                    none
% 2.21/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.21/0.95  --bmc1_ucm_relax_model                  4
% 2.21/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.21/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/0.95  --bmc1_ucm_layered_model                none
% 2.21/0.95  --bmc1_ucm_max_lemma_size               10
% 2.21/0.95  
% 2.21/0.95  ------ AIG Options
% 2.21/0.95  
% 2.21/0.95  --aig_mode                              false
% 2.21/0.95  
% 2.21/0.95  ------ Instantiation Options
% 2.21/0.95  
% 2.21/0.95  --instantiation_flag                    true
% 2.21/0.95  --inst_sos_flag                         false
% 2.21/0.95  --inst_sos_phase                        true
% 2.21/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/0.95  --inst_lit_sel_side                     none
% 2.21/0.95  --inst_solver_per_active                1400
% 2.21/0.95  --inst_solver_calls_frac                1.
% 2.21/0.95  --inst_passive_queue_type               priority_queues
% 2.21/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/0.95  --inst_passive_queues_freq              [25;2]
% 2.21/0.95  --inst_dismatching                      true
% 2.21/0.95  --inst_eager_unprocessed_to_passive     true
% 2.21/0.95  --inst_prop_sim_given                   true
% 2.21/0.95  --inst_prop_sim_new                     false
% 2.21/0.95  --inst_subs_new                         false
% 2.21/0.95  --inst_eq_res_simp                      false
% 2.21/0.95  --inst_subs_given                       false
% 2.21/0.95  --inst_orphan_elimination               true
% 2.21/0.95  --inst_learning_loop_flag               true
% 2.21/0.95  --inst_learning_start                   3000
% 2.21/0.95  --inst_learning_factor                  2
% 2.21/0.95  --inst_start_prop_sim_after_learn       3
% 2.21/0.95  --inst_sel_renew                        solver
% 2.21/0.95  --inst_lit_activity_flag                true
% 2.21/0.95  --inst_restr_to_given                   false
% 2.21/0.95  --inst_activity_threshold               500
% 2.21/0.95  --inst_out_proof                        true
% 2.21/0.95  
% 2.21/0.95  ------ Resolution Options
% 2.21/0.95  
% 2.21/0.95  --resolution_flag                       false
% 2.21/0.95  --res_lit_sel                           adaptive
% 2.21/0.95  --res_lit_sel_side                      none
% 2.21/0.95  --res_ordering                          kbo
% 2.21/0.95  --res_to_prop_solver                    active
% 2.21/0.95  --res_prop_simpl_new                    false
% 2.21/0.95  --res_prop_simpl_given                  true
% 2.21/0.95  --res_passive_queue_type                priority_queues
% 2.21/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/0.95  --res_passive_queues_freq               [15;5]
% 2.21/0.95  --res_forward_subs                      full
% 2.21/0.95  --res_backward_subs                     full
% 2.21/0.95  --res_forward_subs_resolution           true
% 2.21/0.95  --res_backward_subs_resolution          true
% 2.21/0.95  --res_orphan_elimination                true
% 2.21/0.95  --res_time_limit                        2.
% 2.21/0.95  --res_out_proof                         true
% 2.21/0.95  
% 2.21/0.95  ------ Superposition Options
% 2.21/0.95  
% 2.21/0.95  --superposition_flag                    true
% 2.21/0.95  --sup_passive_queue_type                priority_queues
% 2.21/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.21/0.95  --demod_completeness_check              fast
% 2.21/0.95  --demod_use_ground                      true
% 2.21/0.95  --sup_to_prop_solver                    passive
% 2.21/0.95  --sup_prop_simpl_new                    true
% 2.21/0.95  --sup_prop_simpl_given                  true
% 2.21/0.95  --sup_fun_splitting                     false
% 2.21/0.95  --sup_smt_interval                      50000
% 2.21/0.95  
% 2.21/0.95  ------ Superposition Simplification Setup
% 2.21/0.95  
% 2.21/0.95  --sup_indices_passive                   []
% 2.21/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.95  --sup_full_bw                           [BwDemod]
% 2.21/0.95  --sup_immed_triv                        [TrivRules]
% 2.21/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.95  --sup_immed_bw_main                     []
% 2.21/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/0.95  
% 2.21/0.95  ------ Combination Options
% 2.21/0.95  
% 2.21/0.95  --comb_res_mult                         3
% 2.21/0.95  --comb_sup_mult                         2
% 2.21/0.95  --comb_inst_mult                        10
% 2.21/0.95  
% 2.21/0.95  ------ Debug Options
% 2.21/0.95  
% 2.21/0.95  --dbg_backtrace                         false
% 2.21/0.95  --dbg_dump_prop_clauses                 false
% 2.21/0.95  --dbg_dump_prop_clauses_file            -
% 2.21/0.95  --dbg_out_stat                          false
% 2.21/0.95  
% 2.21/0.95  
% 2.21/0.95  
% 2.21/0.95  
% 2.21/0.95  ------ Proving...
% 2.21/0.95  
% 2.21/0.95  
% 2.21/0.95  % SZS status Theorem for theBenchmark.p
% 2.21/0.95  
% 2.21/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 2.21/0.95  
% 2.21/0.95  fof(f8,axiom,(
% 2.21/0.95    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.21/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/0.96  
% 2.21/0.96  fof(f28,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.96    inference(ennf_transformation,[],[f8])).
% 2.21/0.96  
% 2.21/0.96  fof(f29,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.96    inference(flattening,[],[f28])).
% 2.21/0.96  
% 2.21/0.96  fof(f41,plain,(
% 2.21/0.96    ! [X2,X1,X0] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => (r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_connsp_2(sK0(X0,X1,X2),X0,X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK0(X0,X1,X2))))),
% 2.21/0.96    introduced(choice_axiom,[])).
% 2.21/0.96  
% 2.21/0.96  fof(f42,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_connsp_2(sK0(X0,X1,X2),X0,X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK0(X0,X1,X2))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f41])).
% 2.21/0.96  
% 2.21/0.96  fof(f67,plain,(
% 2.21/0.96    ( ! [X2,X0,X1] : (r1_tarski(sK0(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.96    inference(cnf_transformation,[],[f42])).
% 2.21/0.96  
% 2.21/0.96  fof(f6,axiom,(
% 2.21/0.96    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.21/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/0.96  
% 2.21/0.96  fof(f24,plain,(
% 2.21/0.96    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.96    inference(ennf_transformation,[],[f6])).
% 2.21/0.96  
% 2.21/0.96  fof(f25,plain,(
% 2.21/0.96    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.96    inference(flattening,[],[f24])).
% 2.21/0.96  
% 2.21/0.96  fof(f61,plain,(
% 2.21/0.96    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.96    inference(cnf_transformation,[],[f25])).
% 2.21/0.96  
% 2.21/0.96  fof(f65,plain,(
% 2.21/0.96    ( ! [X2,X0,X1] : (m1_connsp_2(sK0(X0,X1,X2),X0,X1) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.96    inference(cnf_transformation,[],[f42])).
% 2.21/0.96  
% 2.21/0.96  fof(f64,plain,(
% 2.21/0.96    ( ! [X2,X0,X1] : (m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.96    inference(cnf_transformation,[],[f42])).
% 2.21/0.96  
% 2.21/0.96  fof(f14,conjecture,(
% 2.21/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 2.21/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/0.96  
% 2.21/0.96  fof(f15,negated_conjecture,(
% 2.21/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 2.21/0.96    inference(negated_conjecture,[],[f14])).
% 2.21/0.96  
% 2.21/0.96  fof(f39,plain,(
% 2.21/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.21/0.96    inference(ennf_transformation,[],[f15])).
% 2.21/0.96  
% 2.21/0.96  fof(f40,plain,(
% 2.21/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.21/0.96    inference(flattening,[],[f39])).
% 2.21/0.96  
% 2.21/0.96  fof(f46,plain,(
% 2.21/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.21/0.96    inference(nnf_transformation,[],[f40])).
% 2.21/0.96  
% 2.21/0.96  fof(f47,plain,(
% 2.21/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.21/0.96    inference(flattening,[],[f46])).
% 2.21/0.96  
% 2.21/0.96  fof(f54,plain,(
% 2.21/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) | r1_tmap_1(X3,X1,X4,X5)) & sK7 = X5 & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 2.21/0.96    introduced(choice_axiom,[])).
% 2.21/0.96  
% 2.21/0.96  fof(f53,plain,(
% 2.21/0.96    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,sK6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,sK6)) & sK6 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.21/0.96    introduced(choice_axiom,[])).
% 2.21/0.96  
% 2.21/0.96  fof(f52,plain,(
% 2.21/0.96    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6) | ~r1_tmap_1(X3,X1,sK5,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6) | r1_tmap_1(X3,X1,sK5,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 2.21/0.96    introduced(choice_axiom,[])).
% 2.21/0.96  
% 2.21/0.96  fof(f51,plain,(
% 2.21/0.96    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6) | ~r1_tmap_1(sK4,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6) | r1_tmap_1(sK4,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_pre_topc(X2,sK4) & v1_tsep_1(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.21/0.96    introduced(choice_axiom,[])).
% 2.21/0.96  
% 2.21/0.96  fof(f50,plain,(
% 2.21/0.96    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK3,X3) & v1_tsep_1(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.21/0.96    introduced(choice_axiom,[])).
% 2.21/0.96  
% 2.21/0.96  fof(f49,plain,(
% 2.21/0.96    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK2,X4,X5)) & (r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6) | r1_tmap_1(X3,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.21/0.96    introduced(choice_axiom,[])).
% 2.21/0.96  
% 2.21/0.96  fof(f48,plain,(
% 2.21/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.21/0.96    introduced(choice_axiom,[])).
% 2.21/0.96  
% 2.21/0.96  fof(f55,plain,(
% 2.21/0.96    (((((((~r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) | ~r1_tmap_1(sK4,sK2,sK5,sK6)) & (r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) | r1_tmap_1(sK4,sK2,sK5,sK6)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_pre_topc(sK3,sK4) & v1_tsep_1(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.21/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f47,f54,f53,f52,f51,f50,f49,f48])).
% 2.21/0.96  
% 2.21/0.96  fof(f94,plain,(
% 2.21/0.96    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) | r1_tmap_1(sK4,sK2,sK5,sK6)),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f93,plain,(
% 2.21/0.96    sK6 = sK7),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f13,axiom,(
% 2.21/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.21/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/0.96  
% 2.21/0.96  fof(f37,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.96    inference(ennf_transformation,[],[f13])).
% 2.21/0.96  
% 2.21/0.96  fof(f38,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.96    inference(flattening,[],[f37])).
% 2.21/0.96  
% 2.21/0.96  fof(f45,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.96    inference(nnf_transformation,[],[f38])).
% 2.21/0.96  
% 2.21/0.96  fof(f75,plain,(
% 2.21/0.96    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.96    inference(cnf_transformation,[],[f45])).
% 2.21/0.96  
% 2.21/0.96  fof(f100,plain,(
% 2.21/0.96    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.96    inference(equality_resolution,[],[f75])).
% 2.21/0.96  
% 2.21/0.96  fof(f87,plain,(
% 2.21/0.96    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f86,plain,(
% 2.21/0.96    v1_funct_1(sK5)),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f11,axiom,(
% 2.21/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.21/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/0.96  
% 2.21/0.96  fof(f33,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.21/0.96    inference(ennf_transformation,[],[f11])).
% 2.21/0.96  
% 2.21/0.96  fof(f34,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.21/0.96    inference(flattening,[],[f33])).
% 2.21/0.96  
% 2.21/0.96  fof(f72,plain,(
% 2.21/0.96    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.21/0.96    inference(cnf_transformation,[],[f34])).
% 2.21/0.96  
% 2.21/0.96  fof(f79,plain,(
% 2.21/0.96    ~v2_struct_0(sK2)),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f80,plain,(
% 2.21/0.96    v2_pre_topc(sK2)),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f81,plain,(
% 2.21/0.96    l1_pre_topc(sK2)),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f84,plain,(
% 2.21/0.96    ~v2_struct_0(sK4)),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f88,plain,(
% 2.21/0.96    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f76,plain,(
% 2.21/0.96    ~v2_struct_0(sK1)),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f77,plain,(
% 2.21/0.96    v2_pre_topc(sK1)),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f78,plain,(
% 2.21/0.96    l1_pre_topc(sK1)),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f82,plain,(
% 2.21/0.96    ~v2_struct_0(sK3)),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f85,plain,(
% 2.21/0.96    m1_pre_topc(sK4,sK1)),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f90,plain,(
% 2.21/0.96    m1_pre_topc(sK3,sK4)),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f92,plain,(
% 2.21/0.96    m1_subset_1(sK7,u1_struct_0(sK3))),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f91,plain,(
% 2.21/0.96    m1_subset_1(sK6,u1_struct_0(sK4))),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f74,plain,(
% 2.21/0.96    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.96    inference(cnf_transformation,[],[f45])).
% 2.21/0.96  
% 2.21/0.96  fof(f101,plain,(
% 2.21/0.96    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.96    inference(equality_resolution,[],[f74])).
% 2.21/0.96  
% 2.21/0.96  fof(f12,axiom,(
% 2.21/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 2.21/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/0.96  
% 2.21/0.96  fof(f35,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.96    inference(ennf_transformation,[],[f12])).
% 2.21/0.96  
% 2.21/0.96  fof(f36,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.96    inference(flattening,[],[f35])).
% 2.21/0.96  
% 2.21/0.96  fof(f73,plain,(
% 2.21/0.96    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.96    inference(cnf_transformation,[],[f36])).
% 2.21/0.96  
% 2.21/0.96  fof(f99,plain,(
% 2.21/0.96    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.96    inference(equality_resolution,[],[f73])).
% 2.21/0.96  
% 2.21/0.96  fof(f95,plain,(
% 2.21/0.96    ~r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) | ~r1_tmap_1(sK4,sK2,sK5,sK6)),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f4,axiom,(
% 2.21/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.21/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/0.96  
% 2.21/0.96  fof(f21,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.21/0.96    inference(ennf_transformation,[],[f4])).
% 2.21/0.96  
% 2.21/0.96  fof(f59,plain,(
% 2.21/0.96    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.21/0.96    inference(cnf_transformation,[],[f21])).
% 2.21/0.96  
% 2.21/0.96  fof(f2,axiom,(
% 2.21/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.21/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/0.96  
% 2.21/0.96  fof(f18,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.21/0.96    inference(ennf_transformation,[],[f2])).
% 2.21/0.96  
% 2.21/0.96  fof(f19,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.21/0.96    inference(flattening,[],[f18])).
% 2.21/0.96  
% 2.21/0.96  fof(f57,plain,(
% 2.21/0.96    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.21/0.96    inference(cnf_transformation,[],[f19])).
% 2.21/0.96  
% 2.21/0.96  fof(f7,axiom,(
% 2.21/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 2.21/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/0.96  
% 2.21/0.96  fof(f26,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.96    inference(ennf_transformation,[],[f7])).
% 2.21/0.96  
% 2.21/0.96  fof(f27,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.96    inference(flattening,[],[f26])).
% 2.21/0.96  
% 2.21/0.96  fof(f62,plain,(
% 2.21/0.96    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.96    inference(cnf_transformation,[],[f27])).
% 2.21/0.96  
% 2.21/0.96  fof(f9,axiom,(
% 2.21/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.21/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/0.96  
% 2.21/0.96  fof(f30,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.21/0.96    inference(ennf_transformation,[],[f9])).
% 2.21/0.96  
% 2.21/0.96  fof(f31,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.21/0.96    inference(flattening,[],[f30])).
% 2.21/0.96  
% 2.21/0.96  fof(f43,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.21/0.96    inference(nnf_transformation,[],[f31])).
% 2.21/0.96  
% 2.21/0.96  fof(f44,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.21/0.96    inference(flattening,[],[f43])).
% 2.21/0.96  
% 2.21/0.96  fof(f68,plain,(
% 2.21/0.96    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.21/0.96    inference(cnf_transformation,[],[f44])).
% 2.21/0.96  
% 2.21/0.96  fof(f98,plain,(
% 2.21/0.96    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.21/0.96    inference(equality_resolution,[],[f68])).
% 2.21/0.96  
% 2.21/0.96  fof(f10,axiom,(
% 2.21/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.21/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/0.96  
% 2.21/0.96  fof(f32,plain,(
% 2.21/0.96    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.21/0.96    inference(ennf_transformation,[],[f10])).
% 2.21/0.96  
% 2.21/0.96  fof(f71,plain,(
% 2.21/0.96    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.21/0.96    inference(cnf_transformation,[],[f32])).
% 2.21/0.96  
% 2.21/0.96  fof(f89,plain,(
% 2.21/0.96    v1_tsep_1(sK3,sK4)),
% 2.21/0.96    inference(cnf_transformation,[],[f55])).
% 2.21/0.96  
% 2.21/0.96  fof(f1,axiom,(
% 2.21/0.96    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.21/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/0.96  
% 2.21/0.96  fof(f16,plain,(
% 2.21/0.96    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.21/0.96    inference(ennf_transformation,[],[f1])).
% 2.21/0.96  
% 2.21/0.96  fof(f17,plain,(
% 2.21/0.96    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.21/0.96    inference(flattening,[],[f16])).
% 2.21/0.96  
% 2.21/0.96  fof(f56,plain,(
% 2.21/0.96    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.21/0.96    inference(cnf_transformation,[],[f17])).
% 2.21/0.96  
% 2.21/0.96  fof(f3,axiom,(
% 2.21/0.96    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.21/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/0.96  
% 2.21/0.96  fof(f20,plain,(
% 2.21/0.96    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.21/0.96    inference(ennf_transformation,[],[f3])).
% 2.21/0.96  
% 2.21/0.96  fof(f58,plain,(
% 2.21/0.96    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.21/0.96    inference(cnf_transformation,[],[f20])).
% 2.21/0.96  
% 2.21/0.96  fof(f5,axiom,(
% 2.21/0.96    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.21/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/0.96  
% 2.21/0.96  fof(f22,plain,(
% 2.21/0.96    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.21/0.96    inference(ennf_transformation,[],[f5])).
% 2.21/0.96  
% 2.21/0.96  fof(f23,plain,(
% 2.21/0.96    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.21/0.96    inference(flattening,[],[f22])).
% 2.21/0.96  
% 2.21/0.96  fof(f60,plain,(
% 2.21/0.96    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.21/0.96    inference(cnf_transformation,[],[f23])).
% 2.21/0.96  
% 2.21/0.96  cnf(c_7,plain,
% 2.21/0.96      ( ~ m1_connsp_2(X0,X1,X2)
% 2.21/0.96      | r1_tarski(sK0(X1,X2,X0),X0)
% 2.21/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.21/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(cnf_transformation,[],[f67]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_5,plain,
% 2.21/0.96      ( ~ m1_connsp_2(X0,X1,X2)
% 2.21/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.21/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(cnf_transformation,[],[f61]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_260,plain,
% 2.21/0.96      ( r1_tarski(sK0(X1,X2,X0),X0)
% 2.21/0.96      | ~ m1_connsp_2(X0,X1,X2)
% 2.21/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(global_propositional_subsumption,[status(thm)],[c_7,c_5]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_261,plain,
% 2.21/0.96      ( ~ m1_connsp_2(X0,X1,X2)
% 2.21/0.96      | r1_tarski(sK0(X1,X2,X0),X0)
% 2.21/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(renaming,[status(thm)],[c_260]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1560,plain,
% 2.21/0.96      ( ~ m1_connsp_2(X0_56,X0_55,X1_56)
% 2.21/0.96      | r1_tarski(sK0(X0_55,X1_56,X0_56),X0_56)
% 2.21/0.96      | ~ m1_subset_1(X1_56,u1_struct_0(X0_55))
% 2.21/0.96      | v2_struct_0(X0_55)
% 2.21/0.96      | ~ l1_pre_topc(X0_55)
% 2.21/0.96      | ~ v2_pre_topc(X0_55) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_261]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2376,plain,
% 2.21/0.96      ( m1_connsp_2(X0_56,X0_55,X1_56) != iProver_top
% 2.21/0.96      | r1_tarski(sK0(X0_55,X1_56,X0_56),X0_56) = iProver_top
% 2.21/0.96      | m1_subset_1(X1_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | v2_struct_0(X0_55) = iProver_top
% 2.21/0.96      | l1_pre_topc(X0_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(X0_55) != iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_1560]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_9,plain,
% 2.21/0.96      ( ~ m1_connsp_2(X0,X1,X2)
% 2.21/0.96      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 2.21/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.21/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(cnf_transformation,[],[f65]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_246,plain,
% 2.21/0.96      ( m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 2.21/0.96      | ~ m1_connsp_2(X0,X1,X2)
% 2.21/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(global_propositional_subsumption,[status(thm)],[c_9,c_5]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_247,plain,
% 2.21/0.96      ( ~ m1_connsp_2(X0,X1,X2)
% 2.21/0.96      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 2.21/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(renaming,[status(thm)],[c_246]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1562,plain,
% 2.21/0.96      ( ~ m1_connsp_2(X0_56,X0_55,X1_56)
% 2.21/0.96      | m1_connsp_2(sK0(X0_55,X1_56,X0_56),X0_55,X1_56)
% 2.21/0.96      | ~ m1_subset_1(X1_56,u1_struct_0(X0_55))
% 2.21/0.96      | v2_struct_0(X0_55)
% 2.21/0.96      | ~ l1_pre_topc(X0_55)
% 2.21/0.96      | ~ v2_pre_topc(X0_55) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_247]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2374,plain,
% 2.21/0.96      ( m1_connsp_2(X0_56,X0_55,X1_56) != iProver_top
% 2.21/0.96      | m1_connsp_2(sK0(X0_55,X1_56,X0_56),X0_55,X1_56) = iProver_top
% 2.21/0.96      | m1_subset_1(X1_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | v2_struct_0(X0_55) = iProver_top
% 2.21/0.96      | l1_pre_topc(X0_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(X0_55) != iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_1562]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_10,plain,
% 2.21/0.96      ( ~ m1_connsp_2(X0,X1,X2)
% 2.21/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.21/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.21/0.96      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(cnf_transformation,[],[f64]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_239,plain,
% 2.21/0.96      ( ~ m1_connsp_2(X0,X1,X2)
% 2.21/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.21/0.96      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(global_propositional_subsumption,
% 2.21/0.96                [status(thm)],
% 2.21/0.96                [c_10,c_5]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1563,plain,
% 2.21/0.96      ( ~ m1_connsp_2(X0_56,X0_55,X1_56)
% 2.21/0.96      | ~ m1_subset_1(X1_56,u1_struct_0(X0_55))
% 2.21/0.96      | m1_subset_1(sK0(X0_55,X1_56,X0_56),k1_zfmisc_1(u1_struct_0(X0_55)))
% 2.21/0.96      | v2_struct_0(X0_55)
% 2.21/0.96      | ~ l1_pre_topc(X0_55)
% 2.21/0.96      | ~ v2_pre_topc(X0_55) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_239]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2373,plain,
% 2.21/0.96      ( m1_connsp_2(X0_56,X0_55,X1_56) != iProver_top
% 2.21/0.96      | m1_subset_1(X1_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(sK0(X0_55,X1_56,X0_56),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
% 2.21/0.96      | v2_struct_0(X0_55) = iProver_top
% 2.21/0.96      | l1_pre_topc(X0_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(X0_55) != iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_1563]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_21,negated_conjecture,
% 2.21/0.96      ( r1_tmap_1(sK4,sK2,sK5,sK6)
% 2.21/0.96      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
% 2.21/0.96      inference(cnf_transformation,[],[f94]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1580,negated_conjecture,
% 2.21/0.96      ( r1_tmap_1(sK4,sK2,sK5,sK6)
% 2.21/0.96      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_21]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2357,plain,
% 2.21/0.96      ( r1_tmap_1(sK4,sK2,sK5,sK6) = iProver_top
% 2.21/0.96      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_1580]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_22,negated_conjecture,
% 2.21/0.96      ( sK6 = sK7 ),
% 2.21/0.96      inference(cnf_transformation,[],[f93]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1579,negated_conjecture,
% 2.21/0.96      ( sK6 = sK7 ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_22]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2436,plain,
% 2.21/0.96      ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
% 2.21/0.96      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
% 2.21/0.96      inference(light_normalisation,[status(thm)],[c_2357,c_1579]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_18,plain,
% 2.21/0.96      ( r1_tmap_1(X0,X1,X2,X3)
% 2.21/0.96      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.21/0.96      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.21/0.96      | ~ m1_connsp_2(X6,X0,X3)
% 2.21/0.96      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.21/0.96      | ~ m1_pre_topc(X4,X5)
% 2.21/0.96      | ~ m1_pre_topc(X0,X5)
% 2.21/0.96      | ~ m1_pre_topc(X4,X0)
% 2.21/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.21/0.96      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.21/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.21/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.21/0.96      | ~ v1_funct_1(X2)
% 2.21/0.96      | v2_struct_0(X5)
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | v2_struct_0(X4)
% 2.21/0.96      | v2_struct_0(X0)
% 2.21/0.96      | ~ l1_pre_topc(X5)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X5)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(cnf_transformation,[],[f100]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_28,negated_conjecture,
% 2.21/0.96      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 2.21/0.96      inference(cnf_transformation,[],[f87]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_867,plain,
% 2.21/0.96      ( r1_tmap_1(X0,X1,X2,X3)
% 2.21/0.96      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.21/0.96      | ~ m1_connsp_2(X6,X0,X3)
% 2.21/0.96      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.21/0.96      | ~ m1_pre_topc(X0,X5)
% 2.21/0.96      | ~ m1_pre_topc(X4,X0)
% 2.21/0.96      | ~ m1_pre_topc(X4,X5)
% 2.21/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.21/0.96      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.21/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.21/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.21/0.96      | ~ v1_funct_1(X2)
% 2.21/0.96      | v2_struct_0(X0)
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | v2_struct_0(X5)
% 2.21/0.96      | v2_struct_0(X4)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ l1_pre_topc(X5)
% 2.21/0.96      | ~ v2_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X5)
% 2.21/0.96      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.21/0.96      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.21/0.96      | sK5 != X2 ),
% 2.21/0.96      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_868,plain,
% 2.21/0.96      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.21/0.96      | r1_tmap_1(X3,X1,sK5,X4)
% 2.21/0.96      | ~ m1_connsp_2(X5,X3,X4)
% 2.21/0.96      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.21/0.96      | ~ m1_pre_topc(X3,X2)
% 2.21/0.96      | ~ m1_pre_topc(X0,X3)
% 2.21/0.96      | ~ m1_pre_topc(X0,X2)
% 2.21/0.96      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.21/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.21/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.21/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.21/0.96      | ~ v1_funct_1(sK5)
% 2.21/0.96      | v2_struct_0(X3)
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | v2_struct_0(X2)
% 2.21/0.96      | v2_struct_0(X0)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ l1_pre_topc(X2)
% 2.21/0.96      | ~ v2_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X2)
% 2.21/0.96      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.21/0.96      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.21/0.96      inference(unflattening,[status(thm)],[c_867]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_29,negated_conjecture,
% 2.21/0.96      ( v1_funct_1(sK5) ),
% 2.21/0.96      inference(cnf_transformation,[],[f86]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_872,plain,
% 2.21/0.96      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.21/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.21/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.21/0.96      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.21/0.96      | ~ m1_pre_topc(X0,X2)
% 2.21/0.96      | ~ m1_pre_topc(X0,X3)
% 2.21/0.96      | ~ m1_pre_topc(X3,X2)
% 2.21/0.96      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.21/0.96      | ~ m1_connsp_2(X5,X3,X4)
% 2.21/0.96      | r1_tmap_1(X3,X1,sK5,X4)
% 2.21/0.96      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.21/0.96      | v2_struct_0(X3)
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | v2_struct_0(X2)
% 2.21/0.96      | v2_struct_0(X0)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ l1_pre_topc(X2)
% 2.21/0.96      | ~ v2_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X2)
% 2.21/0.96      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.21/0.96      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.21/0.96      inference(global_propositional_subsumption,
% 2.21/0.96                [status(thm)],
% 2.21/0.96                [c_868,c_29]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_873,plain,
% 2.21/0.96      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.21/0.96      | r1_tmap_1(X3,X1,sK5,X4)
% 2.21/0.96      | ~ m1_connsp_2(X5,X3,X4)
% 2.21/0.96      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.21/0.96      | ~ m1_pre_topc(X3,X2)
% 2.21/0.96      | ~ m1_pre_topc(X0,X3)
% 2.21/0.96      | ~ m1_pre_topc(X0,X2)
% 2.21/0.96      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.21/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.21/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.21/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.21/0.96      | v2_struct_0(X0)
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | v2_struct_0(X2)
% 2.21/0.96      | v2_struct_0(X3)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ l1_pre_topc(X2)
% 2.21/0.96      | ~ v2_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X2)
% 2.21/0.96      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.21/0.96      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.21/0.96      inference(renaming,[status(thm)],[c_872]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_16,plain,
% 2.21/0.96      ( ~ m1_pre_topc(X0,X1)
% 2.21/0.96      | ~ m1_pre_topc(X2,X0)
% 2.21/0.96      | m1_pre_topc(X2,X1)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(cnf_transformation,[],[f72]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_920,plain,
% 2.21/0.96      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.21/0.96      | r1_tmap_1(X3,X1,sK5,X4)
% 2.21/0.96      | ~ m1_connsp_2(X5,X3,X4)
% 2.21/0.96      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.21/0.96      | ~ m1_pre_topc(X3,X2)
% 2.21/0.96      | ~ m1_pre_topc(X0,X3)
% 2.21/0.96      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.21/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.21/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.21/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.21/0.96      | v2_struct_0(X0)
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | v2_struct_0(X2)
% 2.21/0.96      | v2_struct_0(X3)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ l1_pre_topc(X2)
% 2.21/0.96      | ~ v2_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X2)
% 2.21/0.96      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.21/0.96      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.21/0.96      inference(forward_subsumption_resolution,
% 2.21/0.96                [status(thm)],
% 2.21/0.96                [c_873,c_16]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1556,plain,
% 2.21/0.96      ( ~ r1_tmap_1(X0_55,X1_55,k3_tmap_1(X2_55,X1_55,X3_55,X0_55,sK5),X0_56)
% 2.21/0.96      | r1_tmap_1(X3_55,X1_55,sK5,X0_56)
% 2.21/0.96      | ~ m1_connsp_2(X1_56,X3_55,X0_56)
% 2.21/0.96      | ~ r1_tarski(X1_56,u1_struct_0(X0_55))
% 2.21/0.96      | ~ m1_pre_topc(X3_55,X2_55)
% 2.21/0.96      | ~ m1_pre_topc(X0_55,X3_55)
% 2.21/0.96      | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X3_55)))
% 2.21/0.96      | ~ m1_subset_1(X0_56,u1_struct_0(X3_55))
% 2.21/0.96      | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
% 2.21/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_55),u1_struct_0(X1_55))))
% 2.21/0.96      | v2_struct_0(X0_55)
% 2.21/0.96      | v2_struct_0(X1_55)
% 2.21/0.96      | v2_struct_0(X2_55)
% 2.21/0.96      | v2_struct_0(X3_55)
% 2.21/0.96      | ~ l1_pre_topc(X1_55)
% 2.21/0.96      | ~ l1_pre_topc(X2_55)
% 2.21/0.96      | ~ v2_pre_topc(X1_55)
% 2.21/0.96      | ~ v2_pre_topc(X2_55)
% 2.21/0.96      | u1_struct_0(X3_55) != u1_struct_0(sK4)
% 2.21/0.96      | u1_struct_0(X1_55) != u1_struct_0(sK2) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_920]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2380,plain,
% 2.21/0.96      ( u1_struct_0(X0_55) != u1_struct_0(sK4)
% 2.21/0.96      | u1_struct_0(X1_55) != u1_struct_0(sK2)
% 2.21/0.96      | r1_tmap_1(X2_55,X1_55,k3_tmap_1(X3_55,X1_55,X0_55,X2_55,sK5),X0_56) != iProver_top
% 2.21/0.96      | r1_tmap_1(X0_55,X1_55,sK5,X0_56) = iProver_top
% 2.21/0.96      | m1_connsp_2(X1_56,X0_55,X0_56) != iProver_top
% 2.21/0.96      | r1_tarski(X1_56,u1_struct_0(X2_55)) != iProver_top
% 2.21/0.96      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 2.21/0.96      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 2.21/0.96      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X2_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 2.21/0.96      | v2_struct_0(X1_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X2_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X3_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X0_55) = iProver_top
% 2.21/0.96      | l1_pre_topc(X1_55) != iProver_top
% 2.21/0.96      | l1_pre_topc(X3_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(X1_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(X3_55) != iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_1556]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3609,plain,
% 2.21/0.96      ( u1_struct_0(X0_55) != u1_struct_0(sK4)
% 2.21/0.96      | r1_tmap_1(X1_55,sK2,k3_tmap_1(X2_55,sK2,X0_55,X1_55,sK5),X0_56) != iProver_top
% 2.21/0.96      | r1_tmap_1(X0_55,sK2,sK5,X0_56) = iProver_top
% 2.21/0.96      | m1_connsp_2(X1_56,X0_55,X0_56) != iProver_top
% 2.21/0.96      | r1_tarski(X1_56,u1_struct_0(X1_55)) != iProver_top
% 2.21/0.96      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.21/0.96      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 2.21/0.96      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK2)))) != iProver_top
% 2.21/0.96      | v2_struct_0(X1_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X0_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X2_55) = iProver_top
% 2.21/0.96      | v2_struct_0(sK2) = iProver_top
% 2.21/0.96      | l1_pre_topc(X2_55) != iProver_top
% 2.21/0.96      | l1_pre_topc(sK2) != iProver_top
% 2.21/0.96      | v2_pre_topc(X2_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(sK2) != iProver_top ),
% 2.21/0.96      inference(equality_resolution,[status(thm)],[c_2380]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_36,negated_conjecture,
% 2.21/0.96      ( ~ v2_struct_0(sK2) ),
% 2.21/0.96      inference(cnf_transformation,[],[f79]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_43,plain,
% 2.21/0.96      ( v2_struct_0(sK2) != iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_35,negated_conjecture,
% 2.21/0.96      ( v2_pre_topc(sK2) ),
% 2.21/0.96      inference(cnf_transformation,[],[f80]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_44,plain,
% 2.21/0.96      ( v2_pre_topc(sK2) = iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_34,negated_conjecture,
% 2.21/0.96      ( l1_pre_topc(sK2) ),
% 2.21/0.96      inference(cnf_transformation,[],[f81]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_45,plain,
% 2.21/0.96      ( l1_pre_topc(sK2) = iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3687,plain,
% 2.21/0.96      ( v2_pre_topc(X2_55) != iProver_top
% 2.21/0.96      | v2_struct_0(X2_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X0_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X1_55) = iProver_top
% 2.21/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK2)))) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 2.21/0.96      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 2.21/0.96      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.21/0.96      | r1_tarski(X1_56,u1_struct_0(X1_55)) != iProver_top
% 2.21/0.96      | m1_connsp_2(X1_56,X0_55,X0_56) != iProver_top
% 2.21/0.96      | r1_tmap_1(X0_55,sK2,sK5,X0_56) = iProver_top
% 2.21/0.96      | r1_tmap_1(X1_55,sK2,k3_tmap_1(X2_55,sK2,X0_55,X1_55,sK5),X0_56) != iProver_top
% 2.21/0.96      | u1_struct_0(X0_55) != u1_struct_0(sK4)
% 2.21/0.96      | l1_pre_topc(X2_55) != iProver_top ),
% 2.21/0.96      inference(global_propositional_subsumption,
% 2.21/0.96                [status(thm)],
% 2.21/0.96                [c_3609,c_43,c_44,c_45]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3688,plain,
% 2.21/0.96      ( u1_struct_0(X0_55) != u1_struct_0(sK4)
% 2.21/0.96      | r1_tmap_1(X1_55,sK2,k3_tmap_1(X2_55,sK2,X0_55,X1_55,sK5),X0_56) != iProver_top
% 2.21/0.96      | r1_tmap_1(X0_55,sK2,sK5,X0_56) = iProver_top
% 2.21/0.96      | m1_connsp_2(X1_56,X0_55,X0_56) != iProver_top
% 2.21/0.96      | r1_tarski(X1_56,u1_struct_0(X1_55)) != iProver_top
% 2.21/0.96      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.21/0.96      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 2.21/0.96      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK2)))) != iProver_top
% 2.21/0.96      | v2_struct_0(X1_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X0_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X2_55) = iProver_top
% 2.21/0.96      | l1_pre_topc(X2_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(X2_55) != iProver_top ),
% 2.21/0.96      inference(renaming,[status(thm)],[c_3687]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3707,plain,
% 2.21/0.96      ( r1_tmap_1(X0_55,sK2,k3_tmap_1(X1_55,sK2,sK4,X0_55,sK5),X0_56) != iProver_top
% 2.21/0.96      | r1_tmap_1(sK4,sK2,sK5,X0_56) = iProver_top
% 2.21/0.96      | m1_connsp_2(X1_56,sK4,X0_56) != iProver_top
% 2.21/0.96      | r1_tarski(X1_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_pre_topc(X0_55,sK4) != iProver_top
% 2.21/0.96      | m1_pre_topc(sK4,X1_55) != iProver_top
% 2.21/0.96      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
% 2.21/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.21/0.96      | v2_struct_0(X1_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X0_55) = iProver_top
% 2.21/0.96      | v2_struct_0(sK4) = iProver_top
% 2.21/0.96      | l1_pre_topc(X1_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(X1_55) != iProver_top ),
% 2.21/0.96      inference(equality_resolution,[status(thm)],[c_3688]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_31,negated_conjecture,
% 2.21/0.96      ( ~ v2_struct_0(sK4) ),
% 2.21/0.96      inference(cnf_transformation,[],[f84]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_48,plain,
% 2.21/0.96      ( v2_struct_0(sK4) != iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_27,negated_conjecture,
% 2.21/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 2.21/0.96      inference(cnf_transformation,[],[f88]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_52,plain,
% 2.21/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3824,plain,
% 2.21/0.96      ( v2_struct_0(X0_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X1_55) = iProver_top
% 2.21/0.96      | r1_tmap_1(X0_55,sK2,k3_tmap_1(X1_55,sK2,sK4,X0_55,sK5),X0_56) != iProver_top
% 2.21/0.96      | r1_tmap_1(sK4,sK2,sK5,X0_56) = iProver_top
% 2.21/0.96      | m1_connsp_2(X1_56,sK4,X0_56) != iProver_top
% 2.21/0.96      | r1_tarski(X1_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_pre_topc(X0_55,sK4) != iProver_top
% 2.21/0.96      | m1_pre_topc(sK4,X1_55) != iProver_top
% 2.21/0.96      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
% 2.21/0.96      | l1_pre_topc(X1_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(X1_55) != iProver_top ),
% 2.21/0.96      inference(global_propositional_subsumption,
% 2.21/0.96                [status(thm)],
% 2.21/0.96                [c_3707,c_48,c_52]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3825,plain,
% 2.21/0.96      ( r1_tmap_1(X0_55,sK2,k3_tmap_1(X1_55,sK2,sK4,X0_55,sK5),X0_56) != iProver_top
% 2.21/0.96      | r1_tmap_1(sK4,sK2,sK5,X0_56) = iProver_top
% 2.21/0.96      | m1_connsp_2(X1_56,sK4,X0_56) != iProver_top
% 2.21/0.96      | r1_tarski(X1_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_pre_topc(X0_55,sK4) != iProver_top
% 2.21/0.96      | m1_pre_topc(sK4,X1_55) != iProver_top
% 2.21/0.96      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
% 2.21/0.96      | v2_struct_0(X1_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X0_55) = iProver_top
% 2.21/0.96      | l1_pre_topc(X1_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(X1_55) != iProver_top ),
% 2.21/0.96      inference(renaming,[status(thm)],[c_3824]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3843,plain,
% 2.21/0.96      ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
% 2.21/0.96      | m1_connsp_2(X0_56,sK4,sK7) != iProver_top
% 2.21/0.96      | r1_tarski(X0_56,u1_struct_0(sK3)) != iProver_top
% 2.21/0.96      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.21/0.96      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.21/0.96      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 2.21/0.96      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.21/0.96      | v2_struct_0(sK1) = iProver_top
% 2.21/0.96      | v2_struct_0(sK3) = iProver_top
% 2.21/0.96      | l1_pre_topc(sK1) != iProver_top
% 2.21/0.96      | v2_pre_topc(sK1) != iProver_top ),
% 2.21/0.96      inference(superposition,[status(thm)],[c_2436,c_3825]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_39,negated_conjecture,
% 2.21/0.96      ( ~ v2_struct_0(sK1) ),
% 2.21/0.96      inference(cnf_transformation,[],[f76]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_40,plain,
% 2.21/0.96      ( v2_struct_0(sK1) != iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_38,negated_conjecture,
% 2.21/0.96      ( v2_pre_topc(sK1) ),
% 2.21/0.96      inference(cnf_transformation,[],[f77]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_41,plain,
% 2.21/0.96      ( v2_pre_topc(sK1) = iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_37,negated_conjecture,
% 2.21/0.96      ( l1_pre_topc(sK1) ),
% 2.21/0.96      inference(cnf_transformation,[],[f78]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_42,plain,
% 2.21/0.96      ( l1_pre_topc(sK1) = iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_33,negated_conjecture,
% 2.21/0.96      ( ~ v2_struct_0(sK3) ),
% 2.21/0.96      inference(cnf_transformation,[],[f82]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_46,plain,
% 2.21/0.96      ( v2_struct_0(sK3) != iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_30,negated_conjecture,
% 2.21/0.96      ( m1_pre_topc(sK4,sK1) ),
% 2.21/0.96      inference(cnf_transformation,[],[f85]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_49,plain,
% 2.21/0.96      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_25,negated_conjecture,
% 2.21/0.96      ( m1_pre_topc(sK3,sK4) ),
% 2.21/0.96      inference(cnf_transformation,[],[f90]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_54,plain,
% 2.21/0.96      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_23,negated_conjecture,
% 2.21/0.96      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.21/0.96      inference(cnf_transformation,[],[f92]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_56,plain,
% 2.21/0.96      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_24,negated_conjecture,
% 2.21/0.96      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.21/0.96      inference(cnf_transformation,[],[f91]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1577,negated_conjecture,
% 2.21/0.96      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_24]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2359,plain,
% 2.21/0.96      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_1577]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2407,plain,
% 2.21/0.96      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 2.21/0.96      inference(light_normalisation,[status(thm)],[c_2359,c_1579]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_19,plain,
% 2.21/0.96      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.21/0.96      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.21/0.96      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.21/0.96      | ~ m1_connsp_2(X6,X0,X3)
% 2.21/0.96      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.21/0.96      | ~ m1_pre_topc(X4,X5)
% 2.21/0.96      | ~ m1_pre_topc(X0,X5)
% 2.21/0.96      | ~ m1_pre_topc(X4,X0)
% 2.21/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.21/0.96      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.21/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.21/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.21/0.96      | ~ v1_funct_1(X2)
% 2.21/0.96      | v2_struct_0(X5)
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | v2_struct_0(X4)
% 2.21/0.96      | v2_struct_0(X0)
% 2.21/0.96      | ~ l1_pre_topc(X5)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X5)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(cnf_transformation,[],[f101]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_17,plain,
% 2.21/0.96      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.21/0.96      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.21/0.96      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.21/0.96      | ~ m1_pre_topc(X0,X5)
% 2.21/0.96      | ~ m1_pre_topc(X4,X0)
% 2.21/0.96      | ~ m1_pre_topc(X4,X5)
% 2.21/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.21/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.21/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.21/0.96      | ~ v1_funct_1(X2)
% 2.21/0.96      | v2_struct_0(X5)
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | v2_struct_0(X0)
% 2.21/0.96      | v2_struct_0(X4)
% 2.21/0.96      | ~ l1_pre_topc(X5)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X5)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(cnf_transformation,[],[f99]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_209,plain,
% 2.21/0.96      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.21/0.96      | ~ m1_pre_topc(X4,X0)
% 2.21/0.96      | ~ m1_pre_topc(X0,X5)
% 2.21/0.96      | ~ m1_pre_topc(X4,X5)
% 2.21/0.96      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.21/0.96      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.21/0.96      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.21/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.21/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.21/0.96      | ~ v1_funct_1(X2)
% 2.21/0.96      | v2_struct_0(X5)
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | v2_struct_0(X4)
% 2.21/0.96      | v2_struct_0(X0)
% 2.21/0.96      | ~ l1_pre_topc(X5)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X5)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(global_propositional_subsumption,
% 2.21/0.96                [status(thm)],
% 2.21/0.96                [c_19,c_17]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_210,plain,
% 2.21/0.96      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.21/0.96      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.21/0.96      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.21/0.96      | ~ m1_pre_topc(X0,X5)
% 2.21/0.96      | ~ m1_pre_topc(X4,X0)
% 2.21/0.96      | ~ m1_pre_topc(X4,X5)
% 2.21/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.21/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.21/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.21/0.96      | ~ v1_funct_1(X2)
% 2.21/0.96      | v2_struct_0(X0)
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | v2_struct_0(X5)
% 2.21/0.96      | v2_struct_0(X4)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ l1_pre_topc(X5)
% 2.21/0.96      | ~ v2_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X5) ),
% 2.21/0.96      inference(renaming,[status(thm)],[c_209]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_801,plain,
% 2.21/0.96      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.21/0.96      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.21/0.96      | ~ m1_pre_topc(X0,X5)
% 2.21/0.96      | ~ m1_pre_topc(X4,X0)
% 2.21/0.96      | ~ m1_pre_topc(X4,X5)
% 2.21/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.21/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.21/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.21/0.96      | ~ v1_funct_1(X2)
% 2.21/0.96      | v2_struct_0(X0)
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | v2_struct_0(X5)
% 2.21/0.96      | v2_struct_0(X4)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ l1_pre_topc(X5)
% 2.21/0.96      | ~ v2_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X5)
% 2.21/0.96      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.21/0.96      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.21/0.96      | sK5 != X2 ),
% 2.21/0.96      inference(resolution_lifted,[status(thm)],[c_210,c_28]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_802,plain,
% 2.21/0.96      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.21/0.96      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.21/0.96      | ~ m1_pre_topc(X3,X2)
% 2.21/0.96      | ~ m1_pre_topc(X0,X3)
% 2.21/0.96      | ~ m1_pre_topc(X0,X2)
% 2.21/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.21/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.21/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.21/0.96      | ~ v1_funct_1(sK5)
% 2.21/0.96      | v2_struct_0(X3)
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | v2_struct_0(X2)
% 2.21/0.96      | v2_struct_0(X0)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ l1_pre_topc(X2)
% 2.21/0.96      | ~ v2_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X2)
% 2.21/0.96      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.21/0.96      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.21/0.96      inference(unflattening,[status(thm)],[c_801]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_806,plain,
% 2.21/0.96      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.21/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.21/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.21/0.96      | ~ m1_pre_topc(X0,X2)
% 2.21/0.96      | ~ m1_pre_topc(X0,X3)
% 2.21/0.96      | ~ m1_pre_topc(X3,X2)
% 2.21/0.96      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.21/0.96      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.21/0.96      | v2_struct_0(X3)
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | v2_struct_0(X2)
% 2.21/0.96      | v2_struct_0(X0)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ l1_pre_topc(X2)
% 2.21/0.96      | ~ v2_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X2)
% 2.21/0.96      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.21/0.96      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.21/0.96      inference(global_propositional_subsumption,
% 2.21/0.96                [status(thm)],
% 2.21/0.96                [c_802,c_29]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_807,plain,
% 2.21/0.96      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.21/0.96      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.21/0.96      | ~ m1_pre_topc(X3,X2)
% 2.21/0.96      | ~ m1_pre_topc(X0,X3)
% 2.21/0.96      | ~ m1_pre_topc(X0,X2)
% 2.21/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.21/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.21/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.21/0.96      | v2_struct_0(X0)
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | v2_struct_0(X2)
% 2.21/0.96      | v2_struct_0(X3)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ l1_pre_topc(X2)
% 2.21/0.96      | ~ v2_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X2)
% 2.21/0.96      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.21/0.96      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.21/0.96      inference(renaming,[status(thm)],[c_806]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_848,plain,
% 2.21/0.96      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.21/0.96      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.21/0.96      | ~ m1_pre_topc(X3,X2)
% 2.21/0.96      | ~ m1_pre_topc(X0,X3)
% 2.21/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.21/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.21/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.21/0.96      | v2_struct_0(X0)
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | v2_struct_0(X2)
% 2.21/0.96      | v2_struct_0(X3)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ l1_pre_topc(X2)
% 2.21/0.96      | ~ v2_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X2)
% 2.21/0.96      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.21/0.96      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.21/0.96      inference(forward_subsumption_resolution,
% 2.21/0.96                [status(thm)],
% 2.21/0.96                [c_807,c_16]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1557,plain,
% 2.21/0.96      ( r1_tmap_1(X0_55,X1_55,k3_tmap_1(X2_55,X1_55,X3_55,X0_55,sK5),X0_56)
% 2.21/0.96      | ~ r1_tmap_1(X3_55,X1_55,sK5,X0_56)
% 2.21/0.96      | ~ m1_pre_topc(X3_55,X2_55)
% 2.21/0.96      | ~ m1_pre_topc(X0_55,X3_55)
% 2.21/0.96      | ~ m1_subset_1(X0_56,u1_struct_0(X3_55))
% 2.21/0.96      | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
% 2.21/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_55),u1_struct_0(X1_55))))
% 2.21/0.96      | v2_struct_0(X0_55)
% 2.21/0.96      | v2_struct_0(X1_55)
% 2.21/0.96      | v2_struct_0(X2_55)
% 2.21/0.96      | v2_struct_0(X3_55)
% 2.21/0.96      | ~ l1_pre_topc(X1_55)
% 2.21/0.96      | ~ l1_pre_topc(X2_55)
% 2.21/0.96      | ~ v2_pre_topc(X1_55)
% 2.21/0.96      | ~ v2_pre_topc(X2_55)
% 2.21/0.96      | u1_struct_0(X3_55) != u1_struct_0(sK4)
% 2.21/0.96      | u1_struct_0(X1_55) != u1_struct_0(sK2) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_848]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2379,plain,
% 2.21/0.96      ( u1_struct_0(X0_55) != u1_struct_0(sK4)
% 2.21/0.96      | u1_struct_0(X1_55) != u1_struct_0(sK2)
% 2.21/0.96      | r1_tmap_1(X2_55,X1_55,k3_tmap_1(X3_55,X1_55,X0_55,X2_55,sK5),X0_56) = iProver_top
% 2.21/0.96      | r1_tmap_1(X0_55,X1_55,sK5,X0_56) != iProver_top
% 2.21/0.96      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 2.21/0.96      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X2_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 2.21/0.96      | v2_struct_0(X1_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X2_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X3_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X0_55) = iProver_top
% 2.21/0.96      | l1_pre_topc(X1_55) != iProver_top
% 2.21/0.96      | l1_pre_topc(X3_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(X1_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(X3_55) != iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_1557]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3584,plain,
% 2.21/0.96      ( u1_struct_0(X0_55) != u1_struct_0(sK4)
% 2.21/0.96      | r1_tmap_1(X1_55,sK2,k3_tmap_1(X2_55,sK2,X0_55,X1_55,sK5),X0_56) = iProver_top
% 2.21/0.96      | r1_tmap_1(X0_55,sK2,sK5,X0_56) != iProver_top
% 2.21/0.96      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.21/0.96      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK2)))) != iProver_top
% 2.21/0.96      | v2_struct_0(X1_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X0_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X2_55) = iProver_top
% 2.21/0.96      | v2_struct_0(sK2) = iProver_top
% 2.21/0.96      | l1_pre_topc(X2_55) != iProver_top
% 2.21/0.96      | l1_pre_topc(sK2) != iProver_top
% 2.21/0.96      | v2_pre_topc(X2_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(sK2) != iProver_top ),
% 2.21/0.96      inference(equality_resolution,[status(thm)],[c_2379]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3665,plain,
% 2.21/0.96      ( v2_pre_topc(X2_55) != iProver_top
% 2.21/0.96      | v2_struct_0(X2_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X0_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X1_55) = iProver_top
% 2.21/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK2)))) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
% 2.21/0.96      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 2.21/0.96      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.21/0.96      | r1_tmap_1(X0_55,sK2,sK5,X0_56) != iProver_top
% 2.21/0.96      | r1_tmap_1(X1_55,sK2,k3_tmap_1(X2_55,sK2,X0_55,X1_55,sK5),X0_56) = iProver_top
% 2.21/0.96      | u1_struct_0(X0_55) != u1_struct_0(sK4)
% 2.21/0.96      | l1_pre_topc(X2_55) != iProver_top ),
% 2.21/0.96      inference(global_propositional_subsumption,
% 2.21/0.96                [status(thm)],
% 2.21/0.96                [c_3584,c_43,c_44,c_45]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3666,plain,
% 2.21/0.96      ( u1_struct_0(X0_55) != u1_struct_0(sK4)
% 2.21/0.96      | r1_tmap_1(X1_55,sK2,k3_tmap_1(X2_55,sK2,X0_55,X1_55,sK5),X0_56) = iProver_top
% 2.21/0.96      | r1_tmap_1(X0_55,sK2,sK5,X0_56) != iProver_top
% 2.21/0.96      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.21/0.96      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK2)))) != iProver_top
% 2.21/0.96      | v2_struct_0(X1_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X0_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X2_55) = iProver_top
% 2.21/0.96      | l1_pre_topc(X2_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(X2_55) != iProver_top ),
% 2.21/0.96      inference(renaming,[status(thm)],[c_3665]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3682,plain,
% 2.21/0.96      ( r1_tmap_1(X0_55,sK2,k3_tmap_1(X1_55,sK2,sK4,X0_55,sK5),X0_56) = iProver_top
% 2.21/0.96      | r1_tmap_1(sK4,sK2,sK5,X0_56) != iProver_top
% 2.21/0.96      | m1_pre_topc(X0_55,sK4) != iProver_top
% 2.21/0.96      | m1_pre_topc(sK4,X1_55) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
% 2.21/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.21/0.96      | v2_struct_0(X1_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X0_55) = iProver_top
% 2.21/0.96      | v2_struct_0(sK4) = iProver_top
% 2.21/0.96      | l1_pre_topc(X1_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(X1_55) != iProver_top ),
% 2.21/0.96      inference(equality_resolution,[status(thm)],[c_3666]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3753,plain,
% 2.21/0.96      ( v2_struct_0(X0_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X1_55) = iProver_top
% 2.21/0.96      | r1_tmap_1(X0_55,sK2,k3_tmap_1(X1_55,sK2,sK4,X0_55,sK5),X0_56) = iProver_top
% 2.21/0.96      | r1_tmap_1(sK4,sK2,sK5,X0_56) != iProver_top
% 2.21/0.96      | m1_pre_topc(X0_55,sK4) != iProver_top
% 2.21/0.96      | m1_pre_topc(sK4,X1_55) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
% 2.21/0.96      | l1_pre_topc(X1_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(X1_55) != iProver_top ),
% 2.21/0.96      inference(global_propositional_subsumption,
% 2.21/0.96                [status(thm)],
% 2.21/0.96                [c_3682,c_48,c_52]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3754,plain,
% 2.21/0.96      ( r1_tmap_1(X0_55,sK2,k3_tmap_1(X1_55,sK2,sK4,X0_55,sK5),X0_56) = iProver_top
% 2.21/0.96      | r1_tmap_1(sK4,sK2,sK5,X0_56) != iProver_top
% 2.21/0.96      | m1_pre_topc(X0_55,sK4) != iProver_top
% 2.21/0.96      | m1_pre_topc(sK4,X1_55) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
% 2.21/0.96      | v2_struct_0(X1_55) = iProver_top
% 2.21/0.96      | v2_struct_0(X0_55) = iProver_top
% 2.21/0.96      | l1_pre_topc(X1_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(X1_55) != iProver_top ),
% 2.21/0.96      inference(renaming,[status(thm)],[c_3753]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_20,negated_conjecture,
% 2.21/0.96      ( ~ r1_tmap_1(sK4,sK2,sK5,sK6)
% 2.21/0.96      | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
% 2.21/0.96      inference(cnf_transformation,[],[f95]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1581,negated_conjecture,
% 2.21/0.96      ( ~ r1_tmap_1(sK4,sK2,sK5,sK6)
% 2.21/0.96      | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_20]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2356,plain,
% 2.21/0.96      ( r1_tmap_1(sK4,sK2,sK5,sK6) != iProver_top
% 2.21/0.96      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) != iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_1581]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2447,plain,
% 2.21/0.96      ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
% 2.21/0.96      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) != iProver_top ),
% 2.21/0.96      inference(light_normalisation,[status(thm)],[c_2356,c_1579]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3769,plain,
% 2.21/0.96      ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
% 2.21/0.96      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.21/0.96      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.21/0.96      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 2.21/0.96      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.21/0.96      | v2_struct_0(sK1) = iProver_top
% 2.21/0.96      | v2_struct_0(sK3) = iProver_top
% 2.21/0.96      | l1_pre_topc(sK1) != iProver_top
% 2.21/0.96      | v2_pre_topc(sK1) != iProver_top ),
% 2.21/0.96      inference(superposition,[status(thm)],[c_3754,c_2447]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3873,plain,
% 2.21/0.96      ( m1_connsp_2(X0_56,sK4,sK7) != iProver_top
% 2.21/0.96      | r1_tarski(X0_56,u1_struct_0(sK3)) != iProver_top
% 2.21/0.96      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.21/0.96      inference(global_propositional_subsumption,
% 2.21/0.96                [status(thm)],
% 2.21/0.96                [c_3843,c_40,c_41,c_42,c_46,c_49,c_54,c_56,c_2407,c_3769]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_4068,plain,
% 2.21/0.96      ( m1_connsp_2(X0_56,sK4,X1_56) != iProver_top
% 2.21/0.96      | m1_connsp_2(sK0(sK4,X1_56,X0_56),sK4,sK7) != iProver_top
% 2.21/0.96      | r1_tarski(sK0(sK4,X1_56,X0_56),u1_struct_0(sK3)) != iProver_top
% 2.21/0.96      | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
% 2.21/0.96      | v2_struct_0(sK4) = iProver_top
% 2.21/0.96      | l1_pre_topc(sK4) != iProver_top
% 2.21/0.96      | v2_pre_topc(sK4) != iProver_top ),
% 2.21/0.96      inference(superposition,[status(thm)],[c_2373,c_3873]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3,plain,
% 2.21/0.96      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.21/0.96      inference(cnf_transformation,[],[f59]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1586,plain,
% 2.21/0.96      ( ~ m1_pre_topc(X0_55,X1_55)
% 2.21/0.96      | ~ l1_pre_topc(X1_55)
% 2.21/0.96      | l1_pre_topc(X0_55) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_3]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2720,plain,
% 2.21/0.96      ( ~ m1_pre_topc(sK4,X0_55)
% 2.21/0.96      | ~ l1_pre_topc(X0_55)
% 2.21/0.96      | l1_pre_topc(sK4) ),
% 2.21/0.96      inference(instantiation,[status(thm)],[c_1586]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3013,plain,
% 2.21/0.96      ( ~ m1_pre_topc(sK4,sK1) | l1_pre_topc(sK4) | ~ l1_pre_topc(sK1) ),
% 2.21/0.96      inference(instantiation,[status(thm)],[c_2720]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3014,plain,
% 2.21/0.96      ( m1_pre_topc(sK4,sK1) != iProver_top
% 2.21/0.96      | l1_pre_topc(sK4) = iProver_top
% 2.21/0.96      | l1_pre_topc(sK1) != iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_3013]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1574,negated_conjecture,
% 2.21/0.96      ( m1_pre_topc(sK4,sK1) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_30]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2362,plain,
% 2.21/0.96      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_1574]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1,plain,
% 2.21/0.96      ( ~ m1_pre_topc(X0,X1)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X1)
% 2.21/0.96      | v2_pre_topc(X0) ),
% 2.21/0.96      inference(cnf_transformation,[],[f57]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1587,plain,
% 2.21/0.96      ( ~ m1_pre_topc(X0_55,X1_55)
% 2.21/0.96      | ~ l1_pre_topc(X1_55)
% 2.21/0.96      | ~ v2_pre_topc(X1_55)
% 2.21/0.96      | v2_pre_topc(X0_55) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_1]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2350,plain,
% 2.21/0.96      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 2.21/0.96      | l1_pre_topc(X1_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(X1_55) != iProver_top
% 2.21/0.96      | v2_pre_topc(X0_55) = iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_1587]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3108,plain,
% 2.21/0.96      ( l1_pre_topc(sK1) != iProver_top
% 2.21/0.96      | v2_pre_topc(sK4) = iProver_top
% 2.21/0.96      | v2_pre_topc(sK1) != iProver_top ),
% 2.21/0.96      inference(superposition,[status(thm)],[c_2362,c_2350]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_4185,plain,
% 2.21/0.96      ( m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
% 2.21/0.96      | r1_tarski(sK0(sK4,X1_56,X0_56),u1_struct_0(sK3)) != iProver_top
% 2.21/0.96      | m1_connsp_2(sK0(sK4,X1_56,X0_56),sK4,sK7) != iProver_top
% 2.21/0.96      | m1_connsp_2(X0_56,sK4,X1_56) != iProver_top ),
% 2.21/0.96      inference(global_propositional_subsumption,
% 2.21/0.96                [status(thm)],
% 2.21/0.96                [c_4068,c_41,c_42,c_48,c_49,c_3014,c_3108]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_4186,plain,
% 2.21/0.96      ( m1_connsp_2(X0_56,sK4,X1_56) != iProver_top
% 2.21/0.96      | m1_connsp_2(sK0(sK4,X1_56,X0_56),sK4,sK7) != iProver_top
% 2.21/0.96      | r1_tarski(sK0(sK4,X1_56,X0_56),u1_struct_0(sK3)) != iProver_top
% 2.21/0.96      | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top ),
% 2.21/0.96      inference(renaming,[status(thm)],[c_4185]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_4364,plain,
% 2.21/0.96      ( m1_connsp_2(X0_56,sK4,sK7) != iProver_top
% 2.21/0.96      | r1_tarski(sK0(sK4,sK7,X0_56),u1_struct_0(sK3)) != iProver_top
% 2.21/0.96      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 2.21/0.96      | v2_struct_0(sK4) = iProver_top
% 2.21/0.96      | l1_pre_topc(sK4) != iProver_top
% 2.21/0.96      | v2_pre_topc(sK4) != iProver_top ),
% 2.21/0.96      inference(superposition,[status(thm)],[c_2374,c_4186]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_4381,plain,
% 2.21/0.96      ( m1_connsp_2(X0_56,sK4,sK7) != iProver_top
% 2.21/0.96      | r1_tarski(sK0(sK4,sK7,X0_56),u1_struct_0(sK3)) != iProver_top ),
% 2.21/0.96      inference(global_propositional_subsumption,
% 2.21/0.96                [status(thm)],
% 2.21/0.96                [c_4364,c_41,c_42,c_48,c_49,c_2407,c_3014,c_3108]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_4389,plain,
% 2.21/0.96      ( m1_connsp_2(u1_struct_0(sK3),sK4,sK7) != iProver_top
% 2.21/0.96      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 2.21/0.96      | v2_struct_0(sK4) = iProver_top
% 2.21/0.96      | l1_pre_topc(sK4) != iProver_top
% 2.21/0.96      | v2_pre_topc(sK4) != iProver_top ),
% 2.21/0.96      inference(superposition,[status(thm)],[c_2376,c_4381]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_6,plain,
% 2.21/0.96      ( m1_connsp_2(X0,X1,X2)
% 2.21/0.96      | ~ v3_pre_topc(X0,X1)
% 2.21/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.21/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.21/0.96      | ~ r2_hidden(X2,X0)
% 2.21/0.96      | v2_struct_0(X1)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(cnf_transformation,[],[f62]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1584,plain,
% 2.21/0.96      ( m1_connsp_2(X0_56,X0_55,X1_56)
% 2.21/0.96      | ~ v3_pre_topc(X0_56,X0_55)
% 2.21/0.96      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(X0_55)))
% 2.21/0.96      | ~ m1_subset_1(X1_56,u1_struct_0(X0_55))
% 2.21/0.96      | ~ r2_hidden(X1_56,X0_56)
% 2.21/0.96      | v2_struct_0(X0_55)
% 2.21/0.96      | ~ l1_pre_topc(X0_55)
% 2.21/0.96      | ~ v2_pre_topc(X0_55) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_6]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3415,plain,
% 2.21/0.96      ( m1_connsp_2(u1_struct_0(sK3),sK4,X0_56)
% 2.21/0.96      | ~ v3_pre_topc(u1_struct_0(sK3),sK4)
% 2.21/0.96      | ~ m1_subset_1(X0_56,u1_struct_0(sK4))
% 2.21/0.96      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.21/0.96      | ~ r2_hidden(X0_56,u1_struct_0(sK3))
% 2.21/0.96      | v2_struct_0(sK4)
% 2.21/0.96      | ~ l1_pre_topc(sK4)
% 2.21/0.96      | ~ v2_pre_topc(sK4) ),
% 2.21/0.96      inference(instantiation,[status(thm)],[c_1584]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_4017,plain,
% 2.21/0.96      ( m1_connsp_2(u1_struct_0(sK3),sK4,sK7)
% 2.21/0.96      | ~ v3_pre_topc(u1_struct_0(sK3),sK4)
% 2.21/0.96      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.21/0.96      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 2.21/0.96      | ~ r2_hidden(sK7,u1_struct_0(sK3))
% 2.21/0.96      | v2_struct_0(sK4)
% 2.21/0.96      | ~ l1_pre_topc(sK4)
% 2.21/0.96      | ~ v2_pre_topc(sK4) ),
% 2.21/0.96      inference(instantiation,[status(thm)],[c_3415]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_4021,plain,
% 2.21/0.96      ( m1_connsp_2(u1_struct_0(sK3),sK4,sK7) = iProver_top
% 2.21/0.96      | v3_pre_topc(u1_struct_0(sK3),sK4) != iProver_top
% 2.21/0.96      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.21/0.96      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 2.21/0.96      | r2_hidden(sK7,u1_struct_0(sK3)) != iProver_top
% 2.21/0.96      | v2_struct_0(sK4) = iProver_top
% 2.21/0.96      | l1_pre_topc(sK4) != iProver_top
% 2.21/0.96      | v2_pre_topc(sK4) != iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_4017]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1576,negated_conjecture,
% 2.21/0.96      ( m1_pre_topc(sK3,sK4) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_25]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2360,plain,
% 2.21/0.96      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_1576]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2351,plain,
% 2.21/0.96      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 2.21/0.96      | l1_pre_topc(X1_55) != iProver_top
% 2.21/0.96      | l1_pre_topc(X0_55) = iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_1586]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3135,plain,
% 2.21/0.96      ( l1_pre_topc(sK4) != iProver_top
% 2.21/0.96      | l1_pre_topc(sK3) = iProver_top ),
% 2.21/0.96      inference(superposition,[status(thm)],[c_2360,c_2351]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_14,plain,
% 2.21/0.96      ( ~ v1_tsep_1(X0,X1)
% 2.21/0.96      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.21/0.96      | ~ m1_pre_topc(X0,X1)
% 2.21/0.96      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(cnf_transformation,[],[f98]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_15,plain,
% 2.21/0.96      ( ~ m1_pre_topc(X0,X1)
% 2.21/0.96      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.21/0.96      | ~ l1_pre_topc(X1) ),
% 2.21/0.96      inference(cnf_transformation,[],[f71]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_218,plain,
% 2.21/0.96      ( ~ m1_pre_topc(X0,X1)
% 2.21/0.96      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.21/0.96      | ~ v1_tsep_1(X0,X1)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(global_propositional_subsumption,
% 2.21/0.96                [status(thm)],
% 2.21/0.96                [c_14,c_15]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_219,plain,
% 2.21/0.96      ( ~ v1_tsep_1(X0,X1)
% 2.21/0.96      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.21/0.96      | ~ m1_pre_topc(X0,X1)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X1) ),
% 2.21/0.96      inference(renaming,[status(thm)],[c_218]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_26,negated_conjecture,
% 2.21/0.96      ( v1_tsep_1(sK3,sK4) ),
% 2.21/0.96      inference(cnf_transformation,[],[f89]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_645,plain,
% 2.21/0.96      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.21/0.96      | ~ m1_pre_topc(X0,X1)
% 2.21/0.96      | ~ l1_pre_topc(X1)
% 2.21/0.96      | ~ v2_pre_topc(X1)
% 2.21/0.96      | sK4 != X1
% 2.21/0.96      | sK3 != X0 ),
% 2.21/0.96      inference(resolution_lifted,[status(thm)],[c_219,c_26]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_646,plain,
% 2.21/0.96      ( v3_pre_topc(u1_struct_0(sK3),sK4)
% 2.21/0.96      | ~ m1_pre_topc(sK3,sK4)
% 2.21/0.96      | ~ l1_pre_topc(sK4)
% 2.21/0.96      | ~ v2_pre_topc(sK4) ),
% 2.21/0.96      inference(unflattening,[status(thm)],[c_645]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_648,plain,
% 2.21/0.96      ( v3_pre_topc(u1_struct_0(sK3),sK4)
% 2.21/0.96      | ~ l1_pre_topc(sK4)
% 2.21/0.96      | ~ v2_pre_topc(sK4) ),
% 2.21/0.96      inference(global_propositional_subsumption,
% 2.21/0.96                [status(thm)],
% 2.21/0.96                [c_646,c_25]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1558,plain,
% 2.21/0.96      ( v3_pre_topc(u1_struct_0(sK3),sK4)
% 2.21/0.96      | ~ l1_pre_topc(sK4)
% 2.21/0.96      | ~ v2_pre_topc(sK4) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_648]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2378,plain,
% 2.21/0.96      ( v3_pre_topc(u1_struct_0(sK3),sK4) = iProver_top
% 2.21/0.96      | l1_pre_topc(sK4) != iProver_top
% 2.21/0.96      | v2_pre_topc(sK4) != iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_1558]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_647,plain,
% 2.21/0.96      ( v3_pre_topc(u1_struct_0(sK3),sK4) = iProver_top
% 2.21/0.96      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.21/0.96      | l1_pre_topc(sK4) != iProver_top
% 2.21/0.96      | v2_pre_topc(sK4) != iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_646]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_3073,plain,
% 2.21/0.96      ( v3_pre_topc(u1_struct_0(sK3),sK4) = iProver_top
% 2.21/0.96      | v2_pre_topc(sK4) != iProver_top ),
% 2.21/0.96      inference(global_propositional_subsumption,
% 2.21/0.96                [status(thm)],
% 2.21/0.96                [c_2378,c_42,c_49,c_54,c_647,c_3014]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1578,negated_conjecture,
% 2.21/0.96      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_23]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2358,plain,
% 2.21/0.96      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_1578]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_0,plain,
% 2.21/0.96      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.21/0.96      inference(cnf_transformation,[],[f56]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1588,plain,
% 2.21/0.96      ( ~ m1_subset_1(X0_56,X1_56)
% 2.21/0.96      | r2_hidden(X0_56,X1_56)
% 2.21/0.96      | v1_xboole_0(X1_56) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_0]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2349,plain,
% 2.21/0.96      ( m1_subset_1(X0_56,X1_56) != iProver_top
% 2.21/0.96      | r2_hidden(X0_56,X1_56) = iProver_top
% 2.21/0.96      | v1_xboole_0(X1_56) = iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_1588]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2989,plain,
% 2.21/0.96      ( r2_hidden(sK7,u1_struct_0(sK3)) = iProver_top
% 2.21/0.96      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.21/0.96      inference(superposition,[status(thm)],[c_2358,c_2349]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2,plain,
% 2.21/0.96      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 2.21/0.96      inference(cnf_transformation,[],[f58]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_4,plain,
% 2.21/0.96      ( v2_struct_0(X0)
% 2.21/0.96      | ~ l1_struct_0(X0)
% 2.21/0.96      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.21/0.96      inference(cnf_transformation,[],[f60]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_528,plain,
% 2.21/0.96      ( v2_struct_0(X0)
% 2.21/0.96      | ~ l1_pre_topc(X0)
% 2.21/0.96      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.21/0.96      inference(resolution,[status(thm)],[c_2,c_4]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1559,plain,
% 2.21/0.96      ( v2_struct_0(X0_55)
% 2.21/0.96      | ~ l1_pre_topc(X0_55)
% 2.21/0.96      | ~ v1_xboole_0(u1_struct_0(X0_55)) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_528]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2865,plain,
% 2.21/0.96      ( v2_struct_0(sK3)
% 2.21/0.96      | ~ l1_pre_topc(sK3)
% 2.21/0.96      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.21/0.96      inference(instantiation,[status(thm)],[c_1559]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2866,plain,
% 2.21/0.96      ( v2_struct_0(sK3) = iProver_top
% 2.21/0.96      | l1_pre_topc(sK3) != iProver_top
% 2.21/0.96      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_2865]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_1583,plain,
% 2.21/0.96      ( ~ m1_pre_topc(X0_55,X1_55)
% 2.21/0.96      | m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(u1_struct_0(X1_55)))
% 2.21/0.96      | ~ l1_pre_topc(X1_55) ),
% 2.21/0.96      inference(subtyping,[status(esa)],[c_15]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2727,plain,
% 2.21/0.96      ( ~ m1_pre_topc(sK3,sK4)
% 2.21/0.96      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.21/0.96      | ~ l1_pre_topc(sK4) ),
% 2.21/0.96      inference(instantiation,[status(thm)],[c_1583]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(c_2728,plain,
% 2.21/0.96      ( m1_pre_topc(sK3,sK4) != iProver_top
% 2.21/0.96      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.21/0.96      | l1_pre_topc(sK4) != iProver_top ),
% 2.21/0.96      inference(predicate_to_equality,[status(thm)],[c_2727]) ).
% 2.21/0.96  
% 2.21/0.96  cnf(contradiction,plain,
% 2.21/0.96      ( $false ),
% 2.21/0.96      inference(minisat,
% 2.21/0.96                [status(thm)],
% 2.21/0.96                [c_4389,c_4021,c_3135,c_3108,c_3073,c_3014,c_2989,c_2866,
% 2.21/0.96                 c_2728,c_2407,c_54,c_49,c_48,c_46,c_42,c_41]) ).
% 2.21/0.96  
% 2.21/0.96  
% 2.21/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 2.21/0.96  
% 2.21/0.96  ------                               Statistics
% 2.21/0.96  
% 2.21/0.96  ------ General
% 2.21/0.96  
% 2.21/0.96  abstr_ref_over_cycles:                  0
% 2.21/0.96  abstr_ref_under_cycles:                 0
% 2.21/0.96  gc_basic_clause_elim:                   0
% 2.21/0.96  forced_gc_time:                         0
% 2.21/0.96  parsing_time:                           0.011
% 2.21/0.96  unif_index_cands_time:                  0.
% 2.21/0.96  unif_index_add_time:                    0.
% 2.21/0.96  orderings_time:                         0.
% 2.21/0.96  out_proof_time:                         0.016
% 2.21/0.96  total_time:                             0.171
% 2.21/0.96  num_of_symbols:                         60
% 2.21/0.96  num_of_terms:                           2919
% 2.21/0.96  
% 2.21/0.96  ------ Preprocessing
% 2.21/0.96  
% 2.21/0.96  num_of_splits:                          0
% 2.21/0.96  num_of_split_atoms:                     0
% 2.21/0.96  num_of_reused_defs:                     0
% 2.21/0.96  num_eq_ax_congr_red:                    36
% 2.21/0.96  num_of_sem_filtered_clauses:            1
% 2.21/0.96  num_of_subtypes:                        2
% 2.21/0.96  monotx_restored_types:                  0
% 2.21/0.96  sat_num_of_epr_types:                   0
% 2.21/0.96  sat_num_of_non_cyclic_types:            0
% 2.21/0.96  sat_guarded_non_collapsed_types:        0
% 2.21/0.96  num_pure_diseq_elim:                    0
% 2.21/0.96  simp_replaced_by:                       0
% 2.21/0.96  res_preprocessed:                       161
% 2.21/0.96  prep_upred:                             0
% 2.21/0.96  prep_unflattend:                        27
% 2.21/0.96  smt_new_axioms:                         0
% 2.21/0.96  pred_elim_cands:                        11
% 2.21/0.96  pred_elim:                              4
% 2.21/0.96  pred_elim_cl:                           6
% 2.21/0.96  pred_elim_cycles:                       13
% 2.21/0.96  merged_defs:                            8
% 2.21/0.96  merged_defs_ncl:                        0
% 2.21/0.96  bin_hyper_res:                          8
% 2.21/0.96  prep_cycles:                            4
% 2.21/0.96  pred_elim_time:                         0.023
% 2.21/0.96  splitting_time:                         0.
% 2.21/0.96  sem_filter_time:                        0.
% 2.21/0.96  monotx_time:                            0.
% 2.21/0.96  subtype_inf_time:                       0.
% 2.21/0.96  
% 2.21/0.96  ------ Problem properties
% 2.21/0.96  
% 2.21/0.96  clauses:                                33
% 2.21/0.96  conjectures:                            17
% 2.21/0.96  epr:                                    16
% 2.21/0.96  horn:                                   23
% 2.21/0.96  ground:                                 18
% 2.21/0.96  unary:                                  15
% 2.21/0.96  binary:                                 2
% 2.21/0.96  lits:                                   124
% 2.21/0.96  lits_eq:                                5
% 2.21/0.96  fd_pure:                                0
% 2.21/0.96  fd_pseudo:                              0
% 2.21/0.96  fd_cond:                                0
% 2.21/0.96  fd_pseudo_cond:                         0
% 2.21/0.96  ac_symbols:                             0
% 2.21/0.96  
% 2.21/0.96  ------ Propositional Solver
% 2.21/0.96  
% 2.21/0.96  prop_solver_calls:                      28
% 2.21/0.96  prop_fast_solver_calls:                 1901
% 2.21/0.96  smt_solver_calls:                       0
% 2.21/0.96  smt_fast_solver_calls:                  0
% 2.21/0.96  prop_num_of_clauses:                    985
% 2.21/0.96  prop_preprocess_simplified:             4622
% 2.21/0.96  prop_fo_subsumed:                       71
% 2.21/0.96  prop_solver_time:                       0.
% 2.21/0.96  smt_solver_time:                        0.
% 2.21/0.96  smt_fast_solver_time:                   0.
% 2.21/0.96  prop_fast_solver_time:                  0.
% 2.21/0.96  prop_unsat_core_time:                   0.
% 2.21/0.96  
% 2.21/0.96  ------ QBF
% 2.21/0.96  
% 2.21/0.96  qbf_q_res:                              0
% 2.21/0.96  qbf_num_tautologies:                    0
% 2.21/0.96  qbf_prep_cycles:                        0
% 2.21/0.96  
% 2.21/0.96  ------ BMC1
% 2.21/0.96  
% 2.21/0.96  bmc1_current_bound:                     -1
% 2.21/0.96  bmc1_last_solved_bound:                 -1
% 2.21/0.96  bmc1_unsat_core_size:                   -1
% 2.21/0.96  bmc1_unsat_core_parents_size:           -1
% 2.21/0.96  bmc1_merge_next_fun:                    0
% 2.21/0.96  bmc1_unsat_core_clauses_time:           0.
% 2.21/0.96  
% 2.21/0.96  ------ Instantiation
% 2.21/0.96  
% 2.21/0.96  inst_num_of_clauses:                    276
% 2.21/0.96  inst_num_in_passive:                    39
% 2.21/0.96  inst_num_in_active:                     221
% 2.21/0.96  inst_num_in_unprocessed:                16
% 2.21/0.96  inst_num_of_loops:                      270
% 2.21/0.96  inst_num_of_learning_restarts:          0
% 2.21/0.96  inst_num_moves_active_passive:          42
% 2.21/0.96  inst_lit_activity:                      0
% 2.21/0.96  inst_lit_activity_moves:                0
% 2.21/0.96  inst_num_tautologies:                   0
% 2.21/0.96  inst_num_prop_implied:                  0
% 2.21/0.96  inst_num_existing_simplified:           0
% 2.21/0.96  inst_num_eq_res_simplified:             0
% 2.21/0.96  inst_num_child_elim:                    0
% 2.21/0.96  inst_num_of_dismatching_blockings:      10
% 2.21/0.96  inst_num_of_non_proper_insts:           274
% 2.21/0.96  inst_num_of_duplicates:                 0
% 2.21/0.96  inst_inst_num_from_inst_to_res:         0
% 2.21/0.96  inst_dismatching_checking_time:         0.
% 2.21/0.96  
% 2.21/0.96  ------ Resolution
% 2.21/0.96  
% 2.21/0.96  res_num_of_clauses:                     0
% 2.21/0.96  res_num_in_passive:                     0
% 2.21/0.96  res_num_in_active:                      0
% 2.21/0.96  res_num_of_loops:                       165
% 2.21/0.96  res_forward_subset_subsumed:            56
% 2.21/0.96  res_backward_subset_subsumed:           2
% 2.21/0.96  res_forward_subsumed:                   0
% 2.21/0.96  res_backward_subsumed:                  0
% 2.21/0.96  res_forward_subsumption_resolution:     3
% 2.21/0.96  res_backward_subsumption_resolution:    0
% 2.21/0.96  res_clause_to_clause_subsumption:       207
% 2.21/0.96  res_orphan_elimination:                 0
% 2.21/0.96  res_tautology_del:                      83
% 2.21/0.96  res_num_eq_res_simplified:              0
% 2.21/0.96  res_num_sel_changes:                    0
% 2.21/0.96  res_moves_from_active_to_pass:          0
% 2.21/0.96  
% 2.21/0.96  ------ Superposition
% 2.21/0.96  
% 2.21/0.96  sup_time_total:                         0.
% 2.21/0.96  sup_time_generating:                    0.
% 2.21/0.96  sup_time_sim_full:                      0.
% 2.21/0.96  sup_time_sim_immed:                     0.
% 2.21/0.96  
% 2.21/0.96  sup_num_of_clauses:                     56
% 2.21/0.96  sup_num_in_active:                      53
% 2.21/0.96  sup_num_in_passive:                     3
% 2.21/0.96  sup_num_of_loops:                       53
% 2.21/0.96  sup_fw_superposition:                   15
% 2.21/0.96  sup_bw_superposition:                   11
% 2.21/0.96  sup_immediate_simplified:               0
% 2.21/0.96  sup_given_eliminated:                   0
% 2.21/0.96  comparisons_done:                       0
% 2.21/0.96  comparisons_avoided:                    0
% 2.21/0.96  
% 2.21/0.96  ------ Simplifications
% 2.21/0.96  
% 2.21/0.96  
% 2.21/0.96  sim_fw_subset_subsumed:                 0
% 2.21/0.96  sim_bw_subset_subsumed:                 2
% 2.21/0.96  sim_fw_subsumed:                        0
% 2.21/0.96  sim_bw_subsumed:                        0
% 2.21/0.96  sim_fw_subsumption_res:                 0
% 2.21/0.96  sim_bw_subsumption_res:                 0
% 2.21/0.96  sim_tautology_del:                      2
% 2.21/0.96  sim_eq_tautology_del:                   0
% 2.21/0.96  sim_eq_res_simp:                        0
% 2.21/0.96  sim_fw_demodulated:                     0
% 2.21/0.96  sim_bw_demodulated:                     0
% 2.21/0.96  sim_light_normalised:                   3
% 2.21/0.96  sim_joinable_taut:                      0
% 2.21/0.96  sim_joinable_simp:                      0
% 2.21/0.96  sim_ac_normalised:                      0
% 2.21/0.96  sim_smt_subsumption:                    0
% 2.21/0.96  
%------------------------------------------------------------------------------
