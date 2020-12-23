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
% DateTime   : Thu Dec  3 12:22:40 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  197 (1216 expanded)
%              Number of clauses        :  106 ( 221 expanded)
%              Number of leaves         :   21 ( 456 expanded)
%              Depth                    :   29
%              Number of atoms          : 1445 (18626 expanded)
%              Number of equality atoms :  228 (1440 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_pre_topc(sK0(X0),X0)
        & ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( v3_pre_topc(sK0(X0),X0)
        & ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f50])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f17,conjecture,(
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
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
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
                      & v1_tsep_1(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( X4 = X5
                             => ( r1_tmap_1(X1,X0,X2,X4)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
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
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
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
    inference(flattening,[],[f46])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
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
    inference(nnf_transformation,[],[f47])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
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
    inference(flattening,[],[f56])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | ~ r1_tmap_1(X1,X0,X2,X4) )
          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | r1_tmap_1(X1,X0,X2,X4) )
          & X4 = X5
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6)
          | ~ r1_tmap_1(X1,X0,X2,X4) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6)
          | r1_tmap_1(X1,X0,X2,X4) )
        & sK6 = X4
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                | ~ r1_tmap_1(X1,X0,X2,X4) )
              & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                | r1_tmap_1(X1,X0,X2,X4) )
              & X4 = X5
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ? [X5] :
            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | ~ r1_tmap_1(X1,X0,X2,sK5) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | r1_tmap_1(X1,X0,X2,sK5) )
            & sK5 = X5
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_subset_1(sK5,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                    | ~ r1_tmap_1(X1,X0,X2,X4) )
                  & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                    | r1_tmap_1(X1,X0,X2,X4) )
                  & X4 = X5
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_pre_topc(X3,X1)
          & v1_tsep_1(X3,X1)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5)
                  | ~ r1_tmap_1(X1,X0,X2,X4) )
                & ( r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5)
                  | r1_tmap_1(X1,X0,X2,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(sK4)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_pre_topc(sK4,X1)
        & v1_tsep_1(sK4,X1)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                        | ~ r1_tmap_1(X1,X0,X2,X4) )
                      & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                        | r1_tmap_1(X1,X0,X2,X4) )
                      & X4 = X5
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_pre_topc(X3,X1)
              & v1_tsep_1(X3,X1)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5)
                      | ~ r1_tmap_1(X1,X0,sK3,X4) )
                    & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5)
                      | r1_tmap_1(X1,X0,sK3,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_pre_topc(X3,X1)
            & v1_tsep_1(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
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
                        ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5)
                          | ~ r1_tmap_1(sK2,X0,X2,X4) )
                        & ( r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5)
                          | r1_tmap_1(sK2,X0,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(sK2)) )
                & m1_pre_topc(X3,sK2)
                & v1_tsep_1(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | ~ r1_tmap_1(X1,X0,X2,X4) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | r1_tmap_1(X1,X0,X2,X4) )
                            & X4 = X5
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
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
                          ( ( ~ r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK1,X2,X4) )
                          & ( r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5)
                            | r1_tmap_1(X1,sK1,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
      | ~ r1_tmap_1(sK2,sK1,sK3,sK5) )
    & ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
      | r1_tmap_1(sK2,sK1,sK3,sK5) )
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_pre_topc(sK4,sK2)
    & v1_tsep_1(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f57,f63,f62,f61,f60,f59,f58])).

fof(f104,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | r1_tmap_1(sK2,sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f103,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f64])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f99,plain,(
    v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f93,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f94,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f100,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f92,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f16,axiom,(
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f112,plain,(
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
    inference(equality_resolution,[],[f88])).

fof(f96,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f64])).

fof(f95,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f8,axiom,(
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

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f89,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f90,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f91,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f97,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f64])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f106,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f113,plain,(
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
    inference(equality_resolution,[],[f87])).

fof(f15,axiom,(
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

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f111,plain,(
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
    inference(equality_resolution,[],[f86])).

fof(f105,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | ~ r1_tmap_1(sK2,sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f72,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f102,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f64])).

fof(f98,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3981,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ v1_xboole_0(sK0(sK4)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2435,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3368,plain,
    ( ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(sK0(sK4))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2435])).

cnf(c_25,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,sK3,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1997,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK5) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2062,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1997,c_26])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_14,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_535,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X3,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X4)
    | X2 != X3
    | X0 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_14])).

cnf(c_536,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_4,c_5])).

cnf(c_549,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_536,c_520])).

cnf(c_17,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_220,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_18])).

cnf(c_221,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_220])).

cnf(c_30,negated_conjecture,
    ( v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_507,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_221,c_30])).

cnf(c_508,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_510,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_508,c_36,c_35,c_29])).

cnf(c_610,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK4) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_549,c_510])).

cnf(c_611,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_615,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_connsp_2(u1_struct_0(sK4),sK2,X0)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_611,c_37,c_36,c_35])).

cnf(c_616,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_615])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f112])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_702,plain,
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
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_703,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v1_funct_1(sK3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_702])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_707,plain,
    ( ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_connsp_2(X4,X2,X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_703,c_34])).

cnf(c_708,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_707])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_749,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_708,c_9])).

cnf(c_885,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK4))
    | X3 != X4
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != X5
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_616,c_749])).

cnf(c_886,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
    | r1_tmap_1(sK2,X1,sK3,X2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | v1_xboole_0(u1_struct_0(sK4))
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_885])).

cnf(c_890,plain,
    ( ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK2)
    | r1_tmap_1(sK2,X1,sK3,X2)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK4))
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_886,c_37,c_36,c_35])).

cnf(c_891,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
    | r1_tmap_1(sK2,X1,sK3,X2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK4))
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_890])).

cnf(c_971,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
    | r1_tmap_1(sK2,X1,sK3,X2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK4))
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_891])).

cnf(c_1211,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
    | r1_tmap_1(sK2,X1,sK3,X2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_971])).

cnf(c_1982,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK2,X0,sK3,X1),X2) != iProver_top
    | r1_tmap_1(sK2,X0,sK3,X2) = iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1211])).

cnf(c_2952,plain,
    ( r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK3,X0),X1) != iProver_top
    | r1_tmap_1(sK2,sK1,sK3,X1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1982])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_41,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_42,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_43,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_49,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3302,plain,
    ( v2_struct_0(X0) = iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
    | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK3,X0),X1) != iProver_top
    | r1_tmap_1(sK2,sK1,sK3,X1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2952,c_41,c_42,c_43,c_49])).

cnf(c_3303,plain,
    ( r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK3,X0),X1) != iProver_top
    | r1_tmap_1(sK2,sK1,sK3,X1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(renaming,[status(thm)],[c_3302])).

cnf(c_3316,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2062,c_3303])).

cnf(c_3330,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3316])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3091,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3093,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_3091])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2893,plain,
    ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f113])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f111])).

cnf(c_210,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_21])).

cnf(c_211,plain,
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
    inference(renaming,[status(thm)],[c_210])).

cnf(c_645,plain,
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
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_211,c_33])).

cnf(c_646,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_645])).

cnf(c_650,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_646,c_34])).

cnf(c_651,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_650])).

cnf(c_686,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_651,c_9])).

cnf(c_1984,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,sK3,X2),X3) = iProver_top
    | r1_tmap_1(X0,X1,sK3,X3) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_2793,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK2,X0,sK3,X1),X2) = iProver_top
    | r1_tmap_1(sK2,X0,sK3,X2) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1984])).

cnf(c_44,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_45,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_46,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2798,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | r1_tmap_1(sK2,X0,sK3,X2) != iProver_top
    | r1_tmap_1(X1,X0,k2_tmap_1(sK2,X0,sK3,X1),X2) = iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2793,c_44,c_45,c_46])).

cnf(c_2799,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK2,X0,sK3,X1),X2) = iProver_top
    | r1_tmap_1(sK2,X0,sK3,X2) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2798])).

cnf(c_2812,plain,
    ( r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK3,X0),X1) = iProver_top
    | r1_tmap_1(sK2,sK1,sK3,X1) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2799])).

cnf(c_2866,plain,
    ( v2_struct_0(X0) = iProver_top
    | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK3,X0),X1) = iProver_top
    | r1_tmap_1(sK2,sK1,sK3,X1) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2812,c_41,c_42,c_43,c_49])).

cnf(c_2867,plain,
    ( r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK3,X0),X1) = iProver_top
    | r1_tmap_1(sK2,sK1,sK3,X1) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2866])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1998,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK5) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2067,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1998,c_26])).

cnf(c_2877,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2867,c_2067])).

cnf(c_2878,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2877])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2593,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2595,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_2593])).

cnf(c_1212,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(sK4))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_971])).

cnf(c_1981,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1212])).

cnf(c_52,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1242,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1212])).

cnf(c_2332,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2333,plain,
    ( m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2332])).

cnf(c_2441,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1981,c_46,c_52,c_1242,c_2333])).

cnf(c_2443,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2441])).

cnf(c_12,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2425,plain,
    ( m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3981,c_3368,c_3330,c_3093,c_2893,c_2878,c_2595,c_2443,c_2425,c_27,c_29,c_31,c_35,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.32/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/0.99  
% 2.32/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.32/0.99  
% 2.32/0.99  ------  iProver source info
% 2.32/0.99  
% 2.32/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.32/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.32/0.99  git: non_committed_changes: false
% 2.32/0.99  git: last_make_outside_of_git: false
% 2.32/0.99  
% 2.32/0.99  ------ 
% 2.32/0.99  
% 2.32/0.99  ------ Input Options
% 2.32/0.99  
% 2.32/0.99  --out_options                           all
% 2.32/0.99  --tptp_safe_out                         true
% 2.32/0.99  --problem_path                          ""
% 2.32/0.99  --include_path                          ""
% 2.32/0.99  --clausifier                            res/vclausify_rel
% 2.32/0.99  --clausifier_options                    --mode clausify
% 2.32/0.99  --stdin                                 false
% 2.32/0.99  --stats_out                             all
% 2.32/0.99  
% 2.32/0.99  ------ General Options
% 2.32/0.99  
% 2.32/0.99  --fof                                   false
% 2.32/0.99  --time_out_real                         305.
% 2.32/0.99  --time_out_virtual                      -1.
% 2.32/0.99  --symbol_type_check                     false
% 2.32/0.99  --clausify_out                          false
% 2.32/0.99  --sig_cnt_out                           false
% 2.32/0.99  --trig_cnt_out                          false
% 2.32/0.99  --trig_cnt_out_tolerance                1.
% 2.32/0.99  --trig_cnt_out_sk_spl                   false
% 2.32/0.99  --abstr_cl_out                          false
% 2.32/0.99  
% 2.32/0.99  ------ Global Options
% 2.32/0.99  
% 2.32/0.99  --schedule                              default
% 2.32/0.99  --add_important_lit                     false
% 2.32/0.99  --prop_solver_per_cl                    1000
% 2.32/0.99  --min_unsat_core                        false
% 2.32/0.99  --soft_assumptions                      false
% 2.32/0.99  --soft_lemma_size                       3
% 2.32/0.99  --prop_impl_unit_size                   0
% 2.32/0.99  --prop_impl_unit                        []
% 2.32/0.99  --share_sel_clauses                     true
% 2.32/0.99  --reset_solvers                         false
% 2.32/0.99  --bc_imp_inh                            [conj_cone]
% 2.32/0.99  --conj_cone_tolerance                   3.
% 2.32/0.99  --extra_neg_conj                        none
% 2.32/0.99  --large_theory_mode                     true
% 2.32/0.99  --prolific_symb_bound                   200
% 2.32/0.99  --lt_threshold                          2000
% 2.32/0.99  --clause_weak_htbl                      true
% 2.32/0.99  --gc_record_bc_elim                     false
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing Options
% 2.32/0.99  
% 2.32/0.99  --preprocessing_flag                    true
% 2.32/0.99  --time_out_prep_mult                    0.1
% 2.32/0.99  --splitting_mode                        input
% 2.32/0.99  --splitting_grd                         true
% 2.32/0.99  --splitting_cvd                         false
% 2.32/0.99  --splitting_cvd_svl                     false
% 2.32/0.99  --splitting_nvd                         32
% 2.32/0.99  --sub_typing                            true
% 2.32/0.99  --prep_gs_sim                           true
% 2.32/0.99  --prep_unflatten                        true
% 2.32/0.99  --prep_res_sim                          true
% 2.32/0.99  --prep_upred                            true
% 2.32/0.99  --prep_sem_filter                       exhaustive
% 2.32/0.99  --prep_sem_filter_out                   false
% 2.32/0.99  --pred_elim                             true
% 2.32/0.99  --res_sim_input                         true
% 2.32/0.99  --eq_ax_congr_red                       true
% 2.32/0.99  --pure_diseq_elim                       true
% 2.32/0.99  --brand_transform                       false
% 2.32/0.99  --non_eq_to_eq                          false
% 2.32/0.99  --prep_def_merge                        true
% 2.32/0.99  --prep_def_merge_prop_impl              false
% 2.32/0.99  --prep_def_merge_mbd                    true
% 2.32/0.99  --prep_def_merge_tr_red                 false
% 2.32/0.99  --prep_def_merge_tr_cl                  false
% 2.32/0.99  --smt_preprocessing                     true
% 2.32/0.99  --smt_ac_axioms                         fast
% 2.32/0.99  --preprocessed_out                      false
% 2.32/0.99  --preprocessed_stats                    false
% 2.32/0.99  
% 2.32/0.99  ------ Abstraction refinement Options
% 2.32/0.99  
% 2.32/0.99  --abstr_ref                             []
% 2.32/0.99  --abstr_ref_prep                        false
% 2.32/0.99  --abstr_ref_until_sat                   false
% 2.32/0.99  --abstr_ref_sig_restrict                funpre
% 2.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/0.99  --abstr_ref_under                       []
% 2.32/0.99  
% 2.32/0.99  ------ SAT Options
% 2.32/0.99  
% 2.32/0.99  --sat_mode                              false
% 2.32/0.99  --sat_fm_restart_options                ""
% 2.32/0.99  --sat_gr_def                            false
% 2.32/0.99  --sat_epr_types                         true
% 2.32/0.99  --sat_non_cyclic_types                  false
% 2.32/0.99  --sat_finite_models                     false
% 2.32/0.99  --sat_fm_lemmas                         false
% 2.32/0.99  --sat_fm_prep                           false
% 2.32/0.99  --sat_fm_uc_incr                        true
% 2.32/0.99  --sat_out_model                         small
% 2.32/0.99  --sat_out_clauses                       false
% 2.32/0.99  
% 2.32/0.99  ------ QBF Options
% 2.32/0.99  
% 2.32/0.99  --qbf_mode                              false
% 2.32/0.99  --qbf_elim_univ                         false
% 2.32/0.99  --qbf_dom_inst                          none
% 2.32/0.99  --qbf_dom_pre_inst                      false
% 2.32/0.99  --qbf_sk_in                             false
% 2.32/0.99  --qbf_pred_elim                         true
% 2.32/0.99  --qbf_split                             512
% 2.32/0.99  
% 2.32/0.99  ------ BMC1 Options
% 2.32/0.99  
% 2.32/0.99  --bmc1_incremental                      false
% 2.32/0.99  --bmc1_axioms                           reachable_all
% 2.32/0.99  --bmc1_min_bound                        0
% 2.32/0.99  --bmc1_max_bound                        -1
% 2.32/0.99  --bmc1_max_bound_default                -1
% 2.32/0.99  --bmc1_symbol_reachability              true
% 2.32/0.99  --bmc1_property_lemmas                  false
% 2.32/0.99  --bmc1_k_induction                      false
% 2.32/0.99  --bmc1_non_equiv_states                 false
% 2.32/0.99  --bmc1_deadlock                         false
% 2.32/0.99  --bmc1_ucm                              false
% 2.32/0.99  --bmc1_add_unsat_core                   none
% 2.32/0.99  --bmc1_unsat_core_children              false
% 2.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/0.99  --bmc1_out_stat                         full
% 2.32/0.99  --bmc1_ground_init                      false
% 2.32/0.99  --bmc1_pre_inst_next_state              false
% 2.32/0.99  --bmc1_pre_inst_state                   false
% 2.32/0.99  --bmc1_pre_inst_reach_state             false
% 2.32/0.99  --bmc1_out_unsat_core                   false
% 2.32/0.99  --bmc1_aig_witness_out                  false
% 2.32/0.99  --bmc1_verbose                          false
% 2.32/0.99  --bmc1_dump_clauses_tptp                false
% 2.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.32/0.99  --bmc1_dump_file                        -
% 2.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.32/0.99  --bmc1_ucm_extend_mode                  1
% 2.32/0.99  --bmc1_ucm_init_mode                    2
% 2.32/0.99  --bmc1_ucm_cone_mode                    none
% 2.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.32/0.99  --bmc1_ucm_relax_model                  4
% 2.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/0.99  --bmc1_ucm_layered_model                none
% 2.32/0.99  --bmc1_ucm_max_lemma_size               10
% 2.32/0.99  
% 2.32/0.99  ------ AIG Options
% 2.32/0.99  
% 2.32/0.99  --aig_mode                              false
% 2.32/0.99  
% 2.32/0.99  ------ Instantiation Options
% 2.32/0.99  
% 2.32/0.99  --instantiation_flag                    true
% 2.32/0.99  --inst_sos_flag                         false
% 2.32/0.99  --inst_sos_phase                        true
% 2.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel_side                     num_symb
% 2.32/0.99  --inst_solver_per_active                1400
% 2.32/0.99  --inst_solver_calls_frac                1.
% 2.32/0.99  --inst_passive_queue_type               priority_queues
% 2.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/0.99  --inst_passive_queues_freq              [25;2]
% 2.32/0.99  --inst_dismatching                      true
% 2.32/0.99  --inst_eager_unprocessed_to_passive     true
% 2.32/0.99  --inst_prop_sim_given                   true
% 2.32/0.99  --inst_prop_sim_new                     false
% 2.32/0.99  --inst_subs_new                         false
% 2.32/0.99  --inst_eq_res_simp                      false
% 2.32/0.99  --inst_subs_given                       false
% 2.32/0.99  --inst_orphan_elimination               true
% 2.32/0.99  --inst_learning_loop_flag               true
% 2.32/0.99  --inst_learning_start                   3000
% 2.32/0.99  --inst_learning_factor                  2
% 2.32/0.99  --inst_start_prop_sim_after_learn       3
% 2.32/0.99  --inst_sel_renew                        solver
% 2.32/0.99  --inst_lit_activity_flag                true
% 2.32/0.99  --inst_restr_to_given                   false
% 2.32/0.99  --inst_activity_threshold               500
% 2.32/0.99  --inst_out_proof                        true
% 2.32/0.99  
% 2.32/0.99  ------ Resolution Options
% 2.32/0.99  
% 2.32/0.99  --resolution_flag                       true
% 2.32/0.99  --res_lit_sel                           adaptive
% 2.32/0.99  --res_lit_sel_side                      none
% 2.32/0.99  --res_ordering                          kbo
% 2.32/0.99  --res_to_prop_solver                    active
% 2.32/0.99  --res_prop_simpl_new                    false
% 2.32/0.99  --res_prop_simpl_given                  true
% 2.32/0.99  --res_passive_queue_type                priority_queues
% 2.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/0.99  --res_passive_queues_freq               [15;5]
% 2.32/0.99  --res_forward_subs                      full
% 2.32/0.99  --res_backward_subs                     full
% 2.32/0.99  --res_forward_subs_resolution           true
% 2.32/0.99  --res_backward_subs_resolution          true
% 2.32/0.99  --res_orphan_elimination                true
% 2.32/0.99  --res_time_limit                        2.
% 2.32/0.99  --res_out_proof                         true
% 2.32/0.99  
% 2.32/0.99  ------ Superposition Options
% 2.32/0.99  
% 2.32/0.99  --superposition_flag                    true
% 2.32/0.99  --sup_passive_queue_type                priority_queues
% 2.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.32/0.99  --demod_completeness_check              fast
% 2.32/0.99  --demod_use_ground                      true
% 2.32/0.99  --sup_to_prop_solver                    passive
% 2.32/0.99  --sup_prop_simpl_new                    true
% 2.32/0.99  --sup_prop_simpl_given                  true
% 2.32/0.99  --sup_fun_splitting                     false
% 2.32/0.99  --sup_smt_interval                      50000
% 2.32/0.99  
% 2.32/0.99  ------ Superposition Simplification Setup
% 2.32/0.99  
% 2.32/0.99  --sup_indices_passive                   []
% 2.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_full_bw                           [BwDemod]
% 2.32/0.99  --sup_immed_triv                        [TrivRules]
% 2.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_immed_bw_main                     []
% 2.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.99  
% 2.32/0.99  ------ Combination Options
% 2.32/0.99  
% 2.32/0.99  --comb_res_mult                         3
% 2.32/0.99  --comb_sup_mult                         2
% 2.32/0.99  --comb_inst_mult                        10
% 2.32/0.99  
% 2.32/0.99  ------ Debug Options
% 2.32/0.99  
% 2.32/0.99  --dbg_backtrace                         false
% 2.32/0.99  --dbg_dump_prop_clauses                 false
% 2.32/0.99  --dbg_dump_prop_clauses_file            -
% 2.32/0.99  --dbg_out_stat                          false
% 2.32/0.99  ------ Parsing...
% 2.32/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.32/0.99  ------ Proving...
% 2.32/0.99  ------ Problem Properties 
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  clauses                                 31
% 2.32/0.99  conjectures                             14
% 2.32/0.99  EPR                                     13
% 2.32/0.99  Horn                                    23
% 2.32/0.99  unary                                   13
% 2.32/0.99  binary                                  2
% 2.32/0.99  lits                                    113
% 2.32/0.99  lits eq                                 7
% 2.32/0.99  fd_pure                                 0
% 2.32/0.99  fd_pseudo                               0
% 2.32/0.99  fd_cond                                 0
% 2.32/0.99  fd_pseudo_cond                          1
% 2.32/0.99  AC symbols                              0
% 2.32/0.99  
% 2.32/0.99  ------ Schedule dynamic 5 is on 
% 2.32/0.99  
% 2.32/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  ------ 
% 2.32/0.99  Current options:
% 2.32/0.99  ------ 
% 2.32/0.99  
% 2.32/0.99  ------ Input Options
% 2.32/0.99  
% 2.32/0.99  --out_options                           all
% 2.32/0.99  --tptp_safe_out                         true
% 2.32/0.99  --problem_path                          ""
% 2.32/0.99  --include_path                          ""
% 2.32/0.99  --clausifier                            res/vclausify_rel
% 2.32/0.99  --clausifier_options                    --mode clausify
% 2.32/0.99  --stdin                                 false
% 2.32/0.99  --stats_out                             all
% 2.32/0.99  
% 2.32/0.99  ------ General Options
% 2.32/0.99  
% 2.32/0.99  --fof                                   false
% 2.32/0.99  --time_out_real                         305.
% 2.32/0.99  --time_out_virtual                      -1.
% 2.32/0.99  --symbol_type_check                     false
% 2.32/0.99  --clausify_out                          false
% 2.32/0.99  --sig_cnt_out                           false
% 2.32/0.99  --trig_cnt_out                          false
% 2.32/0.99  --trig_cnt_out_tolerance                1.
% 2.32/0.99  --trig_cnt_out_sk_spl                   false
% 2.32/0.99  --abstr_cl_out                          false
% 2.32/0.99  
% 2.32/0.99  ------ Global Options
% 2.32/0.99  
% 2.32/0.99  --schedule                              default
% 2.32/0.99  --add_important_lit                     false
% 2.32/0.99  --prop_solver_per_cl                    1000
% 2.32/0.99  --min_unsat_core                        false
% 2.32/0.99  --soft_assumptions                      false
% 2.32/0.99  --soft_lemma_size                       3
% 2.32/0.99  --prop_impl_unit_size                   0
% 2.32/0.99  --prop_impl_unit                        []
% 2.32/0.99  --share_sel_clauses                     true
% 2.32/0.99  --reset_solvers                         false
% 2.32/0.99  --bc_imp_inh                            [conj_cone]
% 2.32/0.99  --conj_cone_tolerance                   3.
% 2.32/0.99  --extra_neg_conj                        none
% 2.32/0.99  --large_theory_mode                     true
% 2.32/0.99  --prolific_symb_bound                   200
% 2.32/0.99  --lt_threshold                          2000
% 2.32/0.99  --clause_weak_htbl                      true
% 2.32/0.99  --gc_record_bc_elim                     false
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing Options
% 2.32/0.99  
% 2.32/0.99  --preprocessing_flag                    true
% 2.32/0.99  --time_out_prep_mult                    0.1
% 2.32/0.99  --splitting_mode                        input
% 2.32/0.99  --splitting_grd                         true
% 2.32/0.99  --splitting_cvd                         false
% 2.32/0.99  --splitting_cvd_svl                     false
% 2.32/0.99  --splitting_nvd                         32
% 2.32/0.99  --sub_typing                            true
% 2.32/0.99  --prep_gs_sim                           true
% 2.32/0.99  --prep_unflatten                        true
% 2.32/0.99  --prep_res_sim                          true
% 2.32/0.99  --prep_upred                            true
% 2.32/0.99  --prep_sem_filter                       exhaustive
% 2.32/0.99  --prep_sem_filter_out                   false
% 2.32/0.99  --pred_elim                             true
% 2.32/0.99  --res_sim_input                         true
% 2.32/0.99  --eq_ax_congr_red                       true
% 2.32/0.99  --pure_diseq_elim                       true
% 2.32/0.99  --brand_transform                       false
% 2.32/0.99  --non_eq_to_eq                          false
% 2.32/0.99  --prep_def_merge                        true
% 2.32/0.99  --prep_def_merge_prop_impl              false
% 2.32/0.99  --prep_def_merge_mbd                    true
% 2.32/0.99  --prep_def_merge_tr_red                 false
% 2.32/0.99  --prep_def_merge_tr_cl                  false
% 2.32/0.99  --smt_preprocessing                     true
% 2.32/0.99  --smt_ac_axioms                         fast
% 2.32/0.99  --preprocessed_out                      false
% 2.32/0.99  --preprocessed_stats                    false
% 2.32/0.99  
% 2.32/0.99  ------ Abstraction refinement Options
% 2.32/0.99  
% 2.32/0.99  --abstr_ref                             []
% 2.32/0.99  --abstr_ref_prep                        false
% 2.32/0.99  --abstr_ref_until_sat                   false
% 2.32/0.99  --abstr_ref_sig_restrict                funpre
% 2.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/0.99  --abstr_ref_under                       []
% 2.32/0.99  
% 2.32/0.99  ------ SAT Options
% 2.32/0.99  
% 2.32/0.99  --sat_mode                              false
% 2.32/0.99  --sat_fm_restart_options                ""
% 2.32/0.99  --sat_gr_def                            false
% 2.32/0.99  --sat_epr_types                         true
% 2.32/0.99  --sat_non_cyclic_types                  false
% 2.32/0.99  --sat_finite_models                     false
% 2.32/0.99  --sat_fm_lemmas                         false
% 2.32/0.99  --sat_fm_prep                           false
% 2.32/0.99  --sat_fm_uc_incr                        true
% 2.32/0.99  --sat_out_model                         small
% 2.32/0.99  --sat_out_clauses                       false
% 2.32/0.99  
% 2.32/0.99  ------ QBF Options
% 2.32/0.99  
% 2.32/0.99  --qbf_mode                              false
% 2.32/0.99  --qbf_elim_univ                         false
% 2.32/0.99  --qbf_dom_inst                          none
% 2.32/0.99  --qbf_dom_pre_inst                      false
% 2.32/0.99  --qbf_sk_in                             false
% 2.32/0.99  --qbf_pred_elim                         true
% 2.32/0.99  --qbf_split                             512
% 2.32/0.99  
% 2.32/0.99  ------ BMC1 Options
% 2.32/0.99  
% 2.32/0.99  --bmc1_incremental                      false
% 2.32/0.99  --bmc1_axioms                           reachable_all
% 2.32/0.99  --bmc1_min_bound                        0
% 2.32/0.99  --bmc1_max_bound                        -1
% 2.32/0.99  --bmc1_max_bound_default                -1
% 2.32/0.99  --bmc1_symbol_reachability              true
% 2.32/0.99  --bmc1_property_lemmas                  false
% 2.32/0.99  --bmc1_k_induction                      false
% 2.32/0.99  --bmc1_non_equiv_states                 false
% 2.32/0.99  --bmc1_deadlock                         false
% 2.32/0.99  --bmc1_ucm                              false
% 2.32/0.99  --bmc1_add_unsat_core                   none
% 2.32/0.99  --bmc1_unsat_core_children              false
% 2.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/0.99  --bmc1_out_stat                         full
% 2.32/0.99  --bmc1_ground_init                      false
% 2.32/0.99  --bmc1_pre_inst_next_state              false
% 2.32/0.99  --bmc1_pre_inst_state                   false
% 2.32/0.99  --bmc1_pre_inst_reach_state             false
% 2.32/0.99  --bmc1_out_unsat_core                   false
% 2.32/0.99  --bmc1_aig_witness_out                  false
% 2.32/0.99  --bmc1_verbose                          false
% 2.32/0.99  --bmc1_dump_clauses_tptp                false
% 2.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.32/0.99  --bmc1_dump_file                        -
% 2.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.32/0.99  --bmc1_ucm_extend_mode                  1
% 2.32/0.99  --bmc1_ucm_init_mode                    2
% 2.32/0.99  --bmc1_ucm_cone_mode                    none
% 2.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.32/0.99  --bmc1_ucm_relax_model                  4
% 2.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/0.99  --bmc1_ucm_layered_model                none
% 2.32/0.99  --bmc1_ucm_max_lemma_size               10
% 2.32/0.99  
% 2.32/0.99  ------ AIG Options
% 2.32/0.99  
% 2.32/0.99  --aig_mode                              false
% 2.32/0.99  
% 2.32/0.99  ------ Instantiation Options
% 2.32/0.99  
% 2.32/0.99  --instantiation_flag                    true
% 2.32/0.99  --inst_sos_flag                         false
% 2.32/0.99  --inst_sos_phase                        true
% 2.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel_side                     none
% 2.32/0.99  --inst_solver_per_active                1400
% 2.32/0.99  --inst_solver_calls_frac                1.
% 2.32/0.99  --inst_passive_queue_type               priority_queues
% 2.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/0.99  --inst_passive_queues_freq              [25;2]
% 2.32/0.99  --inst_dismatching                      true
% 2.32/0.99  --inst_eager_unprocessed_to_passive     true
% 2.32/0.99  --inst_prop_sim_given                   true
% 2.32/0.99  --inst_prop_sim_new                     false
% 2.32/0.99  --inst_subs_new                         false
% 2.32/0.99  --inst_eq_res_simp                      false
% 2.32/0.99  --inst_subs_given                       false
% 2.32/0.99  --inst_orphan_elimination               true
% 2.32/0.99  --inst_learning_loop_flag               true
% 2.32/0.99  --inst_learning_start                   3000
% 2.32/0.99  --inst_learning_factor                  2
% 2.32/0.99  --inst_start_prop_sim_after_learn       3
% 2.32/0.99  --inst_sel_renew                        solver
% 2.32/0.99  --inst_lit_activity_flag                true
% 2.32/0.99  --inst_restr_to_given                   false
% 2.32/0.99  --inst_activity_threshold               500
% 2.32/0.99  --inst_out_proof                        true
% 2.32/0.99  
% 2.32/0.99  ------ Resolution Options
% 2.32/0.99  
% 2.32/0.99  --resolution_flag                       false
% 2.32/0.99  --res_lit_sel                           adaptive
% 2.32/0.99  --res_lit_sel_side                      none
% 2.32/0.99  --res_ordering                          kbo
% 2.32/0.99  --res_to_prop_solver                    active
% 2.32/0.99  --res_prop_simpl_new                    false
% 2.32/0.99  --res_prop_simpl_given                  true
% 2.32/0.99  --res_passive_queue_type                priority_queues
% 2.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/0.99  --res_passive_queues_freq               [15;5]
% 2.32/0.99  --res_forward_subs                      full
% 2.32/0.99  --res_backward_subs                     full
% 2.32/0.99  --res_forward_subs_resolution           true
% 2.32/0.99  --res_backward_subs_resolution          true
% 2.32/0.99  --res_orphan_elimination                true
% 2.32/0.99  --res_time_limit                        2.
% 2.32/0.99  --res_out_proof                         true
% 2.32/0.99  
% 2.32/0.99  ------ Superposition Options
% 2.32/0.99  
% 2.32/0.99  --superposition_flag                    true
% 2.32/0.99  --sup_passive_queue_type                priority_queues
% 2.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.32/0.99  --demod_completeness_check              fast
% 2.32/0.99  --demod_use_ground                      true
% 2.32/0.99  --sup_to_prop_solver                    passive
% 2.32/0.99  --sup_prop_simpl_new                    true
% 2.32/0.99  --sup_prop_simpl_given                  true
% 2.32/0.99  --sup_fun_splitting                     false
% 2.32/0.99  --sup_smt_interval                      50000
% 2.32/0.99  
% 2.32/0.99  ------ Superposition Simplification Setup
% 2.32/0.99  
% 2.32/0.99  --sup_indices_passive                   []
% 2.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_full_bw                           [BwDemod]
% 2.32/0.99  --sup_immed_triv                        [TrivRules]
% 2.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_immed_bw_main                     []
% 2.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.99  
% 2.32/0.99  ------ Combination Options
% 2.32/0.99  
% 2.32/0.99  --comb_res_mult                         3
% 2.32/0.99  --comb_sup_mult                         2
% 2.32/0.99  --comb_inst_mult                        10
% 2.32/0.99  
% 2.32/0.99  ------ Debug Options
% 2.32/0.99  
% 2.32/0.99  --dbg_backtrace                         false
% 2.32/0.99  --dbg_dump_prop_clauses                 false
% 2.32/0.99  --dbg_dump_prop_clauses_file            -
% 2.32/0.99  --dbg_out_stat                          false
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  ------ Proving...
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  % SZS status Theorem for theBenchmark.p
% 2.32/0.99  
% 2.32/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.32/0.99  
% 2.32/0.99  fof(f9,axiom,(
% 2.32/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f19,plain,(
% 2.32/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.32/0.99    inference(pure_predicate_removal,[],[f9])).
% 2.32/0.99  
% 2.32/0.99  fof(f31,plain,(
% 2.32/0.99    ! [X0] : (? [X1] : (v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.32/0.99    inference(ennf_transformation,[],[f19])).
% 2.32/0.99  
% 2.32/0.99  fof(f32,plain,(
% 2.32/0.99    ! [X0] : (? [X1] : (v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/0.99    inference(flattening,[],[f31])).
% 2.32/0.99  
% 2.32/0.99  fof(f50,plain,(
% 2.32/0.99    ! [X0] : (? [X1] : (v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_pre_topc(sK0(X0),X0) & ~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f51,plain,(
% 2.32/0.99    ! [X0] : ((v3_pre_topc(sK0(X0),X0) & ~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f50])).
% 2.32/0.99  
% 2.32/0.99  fof(f76,plain,(
% 2.32/0.99    ( ! [X0] : (~v1_xboole_0(sK0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f51])).
% 2.32/0.99  
% 2.32/0.99  fof(f2,axiom,(
% 2.32/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f20,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.32/0.99    inference(ennf_transformation,[],[f2])).
% 2.32/0.99  
% 2.32/0.99  fof(f68,plain,(
% 2.32/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f20])).
% 2.32/0.99  
% 2.32/0.99  fof(f17,conjecture,(
% 2.32/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f18,negated_conjecture,(
% 2.32/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.32/0.99    inference(negated_conjecture,[],[f17])).
% 2.32/0.99  
% 2.32/0.99  fof(f46,plain,(
% 2.32/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.32/0.99    inference(ennf_transformation,[],[f18])).
% 2.32/0.99  
% 2.32/0.99  fof(f47,plain,(
% 2.32/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.32/0.99    inference(flattening,[],[f46])).
% 2.32/0.99  
% 2.32/0.99  fof(f56,plain,(
% 2.32/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.32/0.99    inference(nnf_transformation,[],[f47])).
% 2.32/0.99  
% 2.32/0.99  fof(f57,plain,(
% 2.32/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.32/0.99    inference(flattening,[],[f56])).
% 2.32/0.99  
% 2.32/0.99  fof(f63,plain,(
% 2.32/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | r1_tmap_1(X1,X0,X2,X4)) & sK6 = X4 & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f62,plain,(
% 2.32/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK5)) & sK5 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK5,u1_struct_0(X1)))) )),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f61,plain,(
% 2.32/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK4,X1) & v1_tsep_1(sK4,X1) & ~v2_struct_0(sK4))) )),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f60,plain,(
% 2.32/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5) | ~r1_tmap_1(X1,X0,sK3,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5) | r1_tmap_1(X1,X0,sK3,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f59,plain,(
% 2.32/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5) | ~r1_tmap_1(sK2,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5) | r1_tmap_1(sK2,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK2))) & m1_pre_topc(X3,sK2) & v1_tsep_1(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f58,plain,(
% 2.32/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5) | ~r1_tmap_1(X1,sK1,X2,X4)) & (r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5) | r1_tmap_1(X1,sK1,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f64,plain,(
% 2.32/0.99    ((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | ~r1_tmap_1(sK2,sK1,sK3,sK5)) & (r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | r1_tmap_1(sK2,sK1,sK3,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK2))) & m1_pre_topc(sK4,sK2) & v1_tsep_1(sK4,sK2) & ~v2_struct_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f57,f63,f62,f61,f60,f59,f58])).
% 2.32/0.99  
% 2.32/0.99  fof(f104,plain,(
% 2.32/0.99    r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | r1_tmap_1(sK2,sK1,sK3,sK5)),
% 2.32/0.99    inference(cnf_transformation,[],[f64])).
% 2.32/0.99  
% 2.32/0.99  fof(f103,plain,(
% 2.32/0.99    sK5 = sK6),
% 2.32/0.99    inference(cnf_transformation,[],[f64])).
% 2.32/0.99  
% 2.32/0.99  fof(f3,axiom,(
% 2.32/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f21,plain,(
% 2.32/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.32/0.99    inference(ennf_transformation,[],[f3])).
% 2.32/0.99  
% 2.32/0.99  fof(f22,plain,(
% 2.32/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.32/0.99    inference(flattening,[],[f21])).
% 2.32/0.99  
% 2.32/0.99  fof(f69,plain,(
% 2.32/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f22])).
% 2.32/0.99  
% 2.32/0.99  fof(f11,axiom,(
% 2.32/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 2.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f35,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.32/0.99    inference(ennf_transformation,[],[f11])).
% 2.32/0.99  
% 2.32/0.99  fof(f36,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/0.99    inference(flattening,[],[f35])).
% 2.32/0.99  
% 2.32/0.99  fof(f79,plain,(
% 2.32/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f36])).
% 2.32/0.99  
% 2.32/0.99  fof(f4,axiom,(
% 2.32/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f23,plain,(
% 2.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.32/0.99    inference(ennf_transformation,[],[f4])).
% 2.32/0.99  
% 2.32/0.99  fof(f24,plain,(
% 2.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.32/0.99    inference(flattening,[],[f23])).
% 2.32/0.99  
% 2.32/0.99  fof(f70,plain,(
% 2.32/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f24])).
% 2.32/0.99  
% 2.32/0.99  fof(f12,axiom,(
% 2.32/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f37,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.32/0.99    inference(ennf_transformation,[],[f12])).
% 2.32/0.99  
% 2.32/0.99  fof(f38,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.32/0.99    inference(flattening,[],[f37])).
% 2.32/0.99  
% 2.32/0.99  fof(f52,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.32/0.99    inference(nnf_transformation,[],[f38])).
% 2.32/0.99  
% 2.32/0.99  fof(f53,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.32/0.99    inference(flattening,[],[f52])).
% 2.32/0.99  
% 2.32/0.99  fof(f80,plain,(
% 2.32/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f53])).
% 2.32/0.99  
% 2.32/0.99  fof(f110,plain,(
% 2.32/0.99    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.32/0.99    inference(equality_resolution,[],[f80])).
% 2.32/0.99  
% 2.32/0.99  fof(f13,axiom,(
% 2.32/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f39,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.32/0.99    inference(ennf_transformation,[],[f13])).
% 2.32/0.99  
% 2.32/0.99  fof(f83,plain,(
% 2.32/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f39])).
% 2.32/0.99  
% 2.32/0.99  fof(f99,plain,(
% 2.32/0.99    v1_tsep_1(sK4,sK2)),
% 2.32/0.99    inference(cnf_transformation,[],[f64])).
% 2.32/0.99  
% 2.32/0.99  fof(f93,plain,(
% 2.32/0.99    v2_pre_topc(sK2)),
% 2.32/0.99    inference(cnf_transformation,[],[f64])).
% 2.32/0.99  
% 2.32/0.99  fof(f94,plain,(
% 2.32/0.99    l1_pre_topc(sK2)),
% 2.32/0.99    inference(cnf_transformation,[],[f64])).
% 2.32/0.99  
% 2.32/0.99  fof(f100,plain,(
% 2.32/0.99    m1_pre_topc(sK4,sK2)),
% 2.32/0.99    inference(cnf_transformation,[],[f64])).
% 2.32/0.99  
% 2.32/0.99  fof(f92,plain,(
% 2.32/0.99    ~v2_struct_0(sK2)),
% 2.32/0.99    inference(cnf_transformation,[],[f64])).
% 2.32/0.99  
% 2.32/0.99  fof(f16,axiom,(
% 2.32/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f44,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.32/0.99    inference(ennf_transformation,[],[f16])).
% 2.32/0.99  
% 2.32/0.99  fof(f45,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/0.99    inference(flattening,[],[f44])).
% 2.32/0.99  
% 2.32/0.99  fof(f55,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/0.99    inference(nnf_transformation,[],[f45])).
% 2.32/0.99  
% 2.32/0.99  fof(f88,plain,(
% 2.32/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f55])).
% 2.32/0.99  
% 2.32/0.99  fof(f112,plain,(
% 2.32/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/0.99    inference(equality_resolution,[],[f88])).
% 2.32/0.99  
% 2.32/0.99  fof(f96,plain,(
% 2.32/0.99    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.32/0.99    inference(cnf_transformation,[],[f64])).
% 2.32/0.99  
% 2.32/0.99  fof(f95,plain,(
% 2.32/0.99    v1_funct_1(sK3)),
% 2.32/0.99    inference(cnf_transformation,[],[f64])).
% 2.32/0.99  
% 2.32/0.99  fof(f8,axiom,(
% 2.32/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f29,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.32/0.99    inference(ennf_transformation,[],[f8])).
% 2.32/0.99  
% 2.32/0.99  fof(f30,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/0.99    inference(flattening,[],[f29])).
% 2.32/0.99  
% 2.32/0.99  fof(f74,plain,(
% 2.32/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f30])).
% 2.32/0.99  
% 2.32/0.99  fof(f89,plain,(
% 2.32/0.99    ~v2_struct_0(sK1)),
% 2.32/0.99    inference(cnf_transformation,[],[f64])).
% 2.32/0.99  
% 2.32/0.99  fof(f90,plain,(
% 2.32/0.99    v2_pre_topc(sK1)),
% 2.32/0.99    inference(cnf_transformation,[],[f64])).
% 2.32/0.99  
% 2.32/0.99  fof(f91,plain,(
% 2.32/0.99    l1_pre_topc(sK1)),
% 2.32/0.99    inference(cnf_transformation,[],[f64])).
% 2.32/0.99  
% 2.32/0.99  fof(f97,plain,(
% 2.32/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.32/0.99    inference(cnf_transformation,[],[f64])).
% 2.32/0.99  
% 2.32/0.99  fof(f5,axiom,(
% 2.32/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f25,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.32/0.99    inference(ennf_transformation,[],[f5])).
% 2.32/0.99  
% 2.32/0.99  fof(f26,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.32/0.99    inference(flattening,[],[f25])).
% 2.32/0.99  
% 2.32/0.99  fof(f71,plain,(
% 2.32/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f26])).
% 2.32/0.99  
% 2.32/0.99  fof(f1,axiom,(
% 2.32/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f48,plain,(
% 2.32/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.32/0.99    inference(nnf_transformation,[],[f1])).
% 2.32/0.99  
% 2.32/0.99  fof(f49,plain,(
% 2.32/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.32/0.99    inference(flattening,[],[f48])).
% 2.32/0.99  
% 2.32/0.99  fof(f66,plain,(
% 2.32/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.32/0.99    inference(cnf_transformation,[],[f49])).
% 2.32/0.99  
% 2.32/0.99  fof(f106,plain,(
% 2.32/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.32/0.99    inference(equality_resolution,[],[f66])).
% 2.32/0.99  
% 2.32/0.99  fof(f87,plain,(
% 2.32/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f55])).
% 2.32/0.99  
% 2.32/0.99  fof(f113,plain,(
% 2.32/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/0.99    inference(equality_resolution,[],[f87])).
% 2.32/0.99  
% 2.32/0.99  fof(f15,axiom,(
% 2.32/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f42,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.32/0.99    inference(ennf_transformation,[],[f15])).
% 2.32/0.99  
% 2.32/0.99  fof(f43,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/0.99    inference(flattening,[],[f42])).
% 2.32/0.99  
% 2.32/0.99  fof(f86,plain,(
% 2.32/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f43])).
% 2.32/0.99  
% 2.32/0.99  fof(f111,plain,(
% 2.32/0.99    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/0.99    inference(equality_resolution,[],[f86])).
% 2.32/0.99  
% 2.32/0.99  fof(f105,plain,(
% 2.32/0.99    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | ~r1_tmap_1(sK2,sK1,sK3,sK5)),
% 2.32/0.99    inference(cnf_transformation,[],[f64])).
% 2.32/0.99  
% 2.32/0.99  fof(f6,axiom,(
% 2.32/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f27,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.32/0.99    inference(ennf_transformation,[],[f6])).
% 2.32/0.99  
% 2.32/0.99  fof(f72,plain,(
% 2.32/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f27])).
% 2.32/0.99  
% 2.32/0.99  fof(f75,plain,(
% 2.32/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f51])).
% 2.32/0.99  
% 2.32/0.99  fof(f102,plain,(
% 2.32/0.99    m1_subset_1(sK6,u1_struct_0(sK4))),
% 2.32/0.99    inference(cnf_transformation,[],[f64])).
% 2.32/0.99  
% 2.32/0.99  fof(f98,plain,(
% 2.32/0.99    ~v2_struct_0(sK4)),
% 2.32/0.99    inference(cnf_transformation,[],[f64])).
% 2.32/0.99  
% 2.32/0.99  cnf(c_11,plain,
% 2.32/0.99      ( v2_struct_0(X0)
% 2.32/0.99      | ~ l1_pre_topc(X0)
% 2.32/0.99      | ~ v2_pre_topc(X0)
% 2.32/0.99      | ~ v1_xboole_0(sK0(X0)) ),
% 2.32/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3981,plain,
% 2.32/0.99      ( v2_struct_0(sK4)
% 2.32/0.99      | ~ l1_pre_topc(sK4)
% 2.32/0.99      | ~ v2_pre_topc(sK4)
% 2.32/0.99      | ~ v1_xboole_0(sK0(sK4)) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3,plain,
% 2.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.32/0.99      | ~ v1_xboole_0(X1)
% 2.32/0.99      | v1_xboole_0(X0) ),
% 2.32/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2435,plain,
% 2.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.32/0.99      | v1_xboole_0(X0)
% 2.32/0.99      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3368,plain,
% 2.32/0.99      ( ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.32/0.99      | v1_xboole_0(sK0(sK4))
% 2.32/0.99      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_2435]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_25,negated_conjecture,
% 2.32/0.99      ( r1_tmap_1(sK2,sK1,sK3,sK5)
% 2.32/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 2.32/0.99      inference(cnf_transformation,[],[f104]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1997,plain,
% 2.32/0.99      ( r1_tmap_1(sK2,sK1,sK3,sK5) = iProver_top
% 2.32/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_26,negated_conjecture,
% 2.32/0.99      ( sK5 = sK6 ),
% 2.32/0.99      inference(cnf_transformation,[],[f103]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2062,plain,
% 2.32/0.99      ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
% 2.32/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
% 2.32/0.99      inference(light_normalisation,[status(thm)],[c_1997,c_26]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4,plain,
% 2.32/0.99      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 2.32/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_14,plain,
% 2.32/0.99      ( m1_connsp_2(X0,X1,X2)
% 2.32/0.99      | ~ v3_pre_topc(X0,X1)
% 2.32/0.99      | ~ r2_hidden(X2,X0)
% 2.32/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X1) ),
% 2.32/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_535,plain,
% 2.32/0.99      ( m1_connsp_2(X0,X1,X2)
% 2.32/0.99      | ~ v3_pre_topc(X0,X1)
% 2.32/0.99      | ~ m1_subset_1(X3,X4)
% 2.32/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | v1_xboole_0(X4)
% 2.32/0.99      | X2 != X3
% 2.32/0.99      | X0 != X4 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_14]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_536,plain,
% 2.32/0.99      ( m1_connsp_2(X0,X1,X2)
% 2.32/0.99      | ~ v3_pre_topc(X0,X1)
% 2.32/0.99      | ~ m1_subset_1(X2,X0)
% 2.32/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | v1_xboole_0(X0) ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_535]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_5,plain,
% 2.32/0.99      ( ~ r2_hidden(X0,X1)
% 2.32/0.99      | m1_subset_1(X0,X2)
% 2.32/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.32/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_520,plain,
% 2.32/0.99      ( ~ m1_subset_1(X0,X1)
% 2.32/0.99      | m1_subset_1(X0,X2)
% 2.32/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.32/0.99      | v1_xboole_0(X1) ),
% 2.32/0.99      inference(resolution,[status(thm)],[c_4,c_5]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_549,plain,
% 2.32/0.99      ( m1_connsp_2(X0,X1,X2)
% 2.32/0.99      | ~ v3_pre_topc(X0,X1)
% 2.32/0.99      | ~ m1_subset_1(X2,X0)
% 2.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | v1_xboole_0(X0) ),
% 2.32/0.99      inference(forward_subsumption_resolution,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_536,c_520]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_17,plain,
% 2.32/0.99      ( ~ v1_tsep_1(X0,X1)
% 2.32/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.32/0.99      | ~ m1_pre_topc(X0,X1)
% 2.32/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X1) ),
% 2.32/0.99      inference(cnf_transformation,[],[f110]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_18,plain,
% 2.32/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.32/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/0.99      | ~ l1_pre_topc(X1) ),
% 2.32/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_220,plain,
% 2.32/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.32/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.32/0.99      | ~ v1_tsep_1(X0,X1)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X1) ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_17,c_18]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_221,plain,
% 2.32/0.99      ( ~ v1_tsep_1(X0,X1)
% 2.32/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.32/0.99      | ~ m1_pre_topc(X0,X1)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X1) ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_220]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_30,negated_conjecture,
% 2.32/0.99      ( v1_tsep_1(sK4,sK2) ),
% 2.32/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_507,plain,
% 2.32/0.99      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.32/0.99      | ~ m1_pre_topc(X0,X1)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | sK2 != X1
% 2.32/0.99      | sK4 != X0 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_221,c_30]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_508,plain,
% 2.32/0.99      ( v3_pre_topc(u1_struct_0(sK4),sK2)
% 2.32/0.99      | ~ m1_pre_topc(sK4,sK2)
% 2.32/0.99      | ~ l1_pre_topc(sK2)
% 2.32/0.99      | ~ v2_pre_topc(sK2) ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_507]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_36,negated_conjecture,
% 2.32/0.99      ( v2_pre_topc(sK2) ),
% 2.32/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_35,negated_conjecture,
% 2.32/0.99      ( l1_pre_topc(sK2) ),
% 2.32/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_29,negated_conjecture,
% 2.32/0.99      ( m1_pre_topc(sK4,sK2) ),
% 2.32/0.99      inference(cnf_transformation,[],[f100]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_510,plain,
% 2.32/0.99      ( v3_pre_topc(u1_struct_0(sK4),sK2) ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_508,c_36,c_35,c_29]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_610,plain,
% 2.32/0.99      ( m1_connsp_2(X0,X1,X2)
% 2.32/0.99      | ~ m1_subset_1(X2,X0)
% 2.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | v1_xboole_0(X0)
% 2.32/0.99      | u1_struct_0(sK4) != X0
% 2.32/0.99      | sK2 != X1 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_549,c_510]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_611,plain,
% 2.32/0.99      ( m1_connsp_2(u1_struct_0(sK4),sK2,X0)
% 2.32/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.32/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/0.99      | v2_struct_0(sK2)
% 2.32/0.99      | ~ l1_pre_topc(sK2)
% 2.32/0.99      | ~ v2_pre_topc(sK2)
% 2.32/0.99      | v1_xboole_0(u1_struct_0(sK4)) ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_610]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_37,negated_conjecture,
% 2.32/0.99      ( ~ v2_struct_0(sK2) ),
% 2.32/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_615,plain,
% 2.32/0.99      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.32/0.99      | m1_connsp_2(u1_struct_0(sK4),sK2,X0)
% 2.32/0.99      | v1_xboole_0(u1_struct_0(sK4)) ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_611,c_37,c_36,c_35]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_616,plain,
% 2.32/0.99      ( m1_connsp_2(u1_struct_0(sK4),sK2,X0)
% 2.32/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.32/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/0.99      | v1_xboole_0(u1_struct_0(sK4)) ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_615]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_22,plain,
% 2.32/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.32/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.32/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.32/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.32/0.99      | ~ m1_pre_topc(X4,X0)
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.32/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.32/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.32/0.99      | ~ v1_funct_1(X2)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | v2_struct_0(X4)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ l1_pre_topc(X0)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X0) ),
% 2.32/0.99      inference(cnf_transformation,[],[f112]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_33,negated_conjecture,
% 2.32/0.99      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 2.32/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_702,plain,
% 2.32/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.32/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.32/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.32/0.99      | ~ m1_pre_topc(X4,X0)
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.32/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.32/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.32/0.99      | ~ v1_funct_1(X2)
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(X4)
% 2.32/0.99      | ~ l1_pre_topc(X0)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X0)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.32/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.32/0.99      | sK3 != X2 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_703,plain,
% 2.32/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.32/0.99      | r1_tmap_1(X2,X1,sK3,X3)
% 2.32/0.99      | ~ m1_connsp_2(X4,X2,X3)
% 2.32/0.99      | ~ m1_pre_topc(X0,X2)
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.32/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.32/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.32/0.99      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.32/0.99      | ~ v1_funct_1(sK3)
% 2.32/0.99      | v2_struct_0(X2)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | ~ l1_pre_topc(X2)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X2)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.32/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_702]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_34,negated_conjecture,
% 2.32/0.99      ( v1_funct_1(sK3) ),
% 2.32/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_707,plain,
% 2.32/0.99      ( ~ r1_tarski(X4,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.32/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_pre_topc(X0,X2)
% 2.32/0.99      | ~ m1_connsp_2(X4,X2,X3)
% 2.32/0.99      | r1_tmap_1(X2,X1,sK3,X3)
% 2.32/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.32/0.99      | v2_struct_0(X2)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | ~ l1_pre_topc(X2)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X2)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.32/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_703,c_34]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_708,plain,
% 2.32/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.32/0.99      | r1_tmap_1(X2,X1,sK3,X3)
% 2.32/0.99      | ~ m1_connsp_2(X4,X2,X3)
% 2.32/0.99      | ~ m1_pre_topc(X0,X2)
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.32/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.32/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.32/0.99      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(X2)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ l1_pre_topc(X2)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X2)
% 2.32/0.99      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.32/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_707]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_9,plain,
% 2.32/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.32/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | ~ l1_pre_topc(X1) ),
% 2.32/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_749,plain,
% 2.32/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.32/0.99      | r1_tmap_1(X2,X1,sK3,X3)
% 2.32/0.99      | ~ m1_connsp_2(X4,X2,X3)
% 2.32/0.99      | ~ m1_pre_topc(X0,X2)
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.32/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.32/0.99      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(X2)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ l1_pre_topc(X2)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X2)
% 2.32/0.99      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.32/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.32/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_708,c_9]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_885,plain,
% 2.32/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.32/0.99      | r1_tmap_1(X2,X1,sK3,X3)
% 2.32/0.99      | ~ m1_pre_topc(X0,X2)
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 2.32/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
% 2.32/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.32/0.99      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | v2_struct_0(X2)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | ~ l1_pre_topc(X2)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X2)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | v1_xboole_0(u1_struct_0(sK4))
% 2.32/0.99      | X3 != X4
% 2.32/0.99      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.32/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.32/0.99      | u1_struct_0(sK4) != X5
% 2.32/0.99      | sK2 != X2 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_616,c_749]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_886,plain,
% 2.32/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
% 2.32/0.99      | r1_tmap_1(sK2,X1,sK3,X2)
% 2.32/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.32/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.32/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.32/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(sK2)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ l1_pre_topc(sK2)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(sK2)
% 2.32/0.99      | v1_xboole_0(u1_struct_0(sK4))
% 2.32/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.32/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_885]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_890,plain,
% 2.32/0.99      ( ~ v2_pre_topc(X1)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.32/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.32/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.32/0.99      | r1_tmap_1(sK2,X1,sK3,X2)
% 2.32/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | v1_xboole_0(u1_struct_0(sK4))
% 2.32/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.32/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_886,c_37,c_36,c_35]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_891,plain,
% 2.32/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
% 2.32/0.99      | r1_tmap_1(sK2,X1,sK3,X2)
% 2.32/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.32/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.32/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.32/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | v1_xboole_0(u1_struct_0(sK4))
% 2.32/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.32/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_890]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_971,plain,
% 2.32/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
% 2.32/0.99      | r1_tmap_1(sK2,X1,sK3,X2)
% 2.32/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.32/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.32/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.32/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | v1_xboole_0(u1_struct_0(sK4))
% 2.32/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.32/0.99      inference(equality_resolution_simp,[status(thm)],[c_891]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1211,plain,
% 2.32/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK2,X1,sK3,X0),X2)
% 2.32/0.99      | r1_tmap_1(sK2,X1,sK3,X2)
% 2.32/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.32/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.32/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.32/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(X0))
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.32/0.99      | ~ sP0_iProver_split ),
% 2.32/0.99      inference(splitting,
% 2.32/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.32/0.99                [c_971]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1982,plain,
% 2.32/0.99      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.32/0.99      | r1_tmap_1(X1,X0,k2_tmap_1(sK2,X0,sK3,X1),X2) != iProver_top
% 2.32/0.99      | r1_tmap_1(sK2,X0,sK3,X2) = iProver_top
% 2.32/0.99      | m1_pre_topc(X1,sK2) != iProver_top
% 2.32/0.99      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 2.32/0.99      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.32/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 2.32/0.99      | r1_tarski(u1_struct_0(sK4),u1_struct_0(X1)) != iProver_top
% 2.32/0.99      | v2_struct_0(X0) = iProver_top
% 2.32/0.99      | v2_struct_0(X1) = iProver_top
% 2.32/0.99      | l1_pre_topc(X0) != iProver_top
% 2.32/0.99      | v2_pre_topc(X0) != iProver_top
% 2.32/0.99      | sP0_iProver_split != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_1211]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2952,plain,
% 2.32/0.99      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK3,X0),X1) != iProver_top
% 2.32/0.99      | r1_tmap_1(sK2,sK1,sK3,X1) = iProver_top
% 2.32/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 2.32/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 2.32/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 2.32/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.32/0.99      | r1_tarski(u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
% 2.32/0.99      | v2_struct_0(X0) = iProver_top
% 2.32/0.99      | v2_struct_0(sK1) = iProver_top
% 2.32/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.32/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.32/0.99      | sP0_iProver_split != iProver_top ),
% 2.32/0.99      inference(equality_resolution,[status(thm)],[c_1982]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_40,negated_conjecture,
% 2.32/0.99      ( ~ v2_struct_0(sK1) ),
% 2.32/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_41,plain,
% 2.32/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_39,negated_conjecture,
% 2.32/0.99      ( v2_pre_topc(sK1) ),
% 2.32/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_42,plain,
% 2.32/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_38,negated_conjecture,
% 2.32/0.99      ( l1_pre_topc(sK1) ),
% 2.32/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_43,plain,
% 2.32/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_32,negated_conjecture,
% 2.32/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 2.32/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_49,plain,
% 2.32/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3302,plain,
% 2.32/0.99      ( v2_struct_0(X0) = iProver_top
% 2.32/0.99      | r1_tarski(u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
% 2.32/0.99      | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK3,X0),X1) != iProver_top
% 2.32/0.99      | r1_tmap_1(sK2,sK1,sK3,X1) = iProver_top
% 2.32/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 2.32/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 2.32/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 2.32/0.99      | sP0_iProver_split != iProver_top ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_2952,c_41,c_42,c_43,c_49]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3303,plain,
% 2.32/0.99      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK3,X0),X1) != iProver_top
% 2.32/0.99      | r1_tmap_1(sK2,sK1,sK3,X1) = iProver_top
% 2.32/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 2.32/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 2.32/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 2.32/0.99      | r1_tarski(u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
% 2.32/0.99      | v2_struct_0(X0) = iProver_top
% 2.32/0.99      | sP0_iProver_split != iProver_top ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_3302]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3316,plain,
% 2.32/0.99      ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
% 2.32/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.32/0.99      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 2.32/0.99      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
% 2.32/0.99      | v2_struct_0(sK4) = iProver_top
% 2.32/0.99      | sP0_iProver_split != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_2062,c_3303]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3330,plain,
% 2.32/0.99      ( r1_tmap_1(sK2,sK1,sK3,sK6)
% 2.32/0.99      | ~ m1_pre_topc(sK4,sK2)
% 2.32/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.32/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
% 2.32/0.99      | v2_struct_0(sK4)
% 2.32/0.99      | ~ sP0_iProver_split ),
% 2.32/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3316]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_6,plain,
% 2.32/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | v2_pre_topc(X0) ),
% 2.32/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3091,plain,
% 2.32/0.99      ( ~ m1_pre_topc(sK4,X0)
% 2.32/0.99      | ~ l1_pre_topc(X0)
% 2.32/0.99      | ~ v2_pre_topc(X0)
% 2.32/0.99      | v2_pre_topc(sK4) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3093,plain,
% 2.32/0.99      ( ~ m1_pre_topc(sK4,sK2)
% 2.32/0.99      | ~ l1_pre_topc(sK2)
% 2.32/0.99      | ~ v2_pre_topc(sK2)
% 2.32/0.99      | v2_pre_topc(sK4) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_3091]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1,plain,
% 2.32/0.99      ( r1_tarski(X0,X0) ),
% 2.32/0.99      inference(cnf_transformation,[],[f106]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2893,plain,
% 2.32/0.99      ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_23,plain,
% 2.32/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.32/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.32/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.32/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.32/0.99      | ~ m1_pre_topc(X4,X0)
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.32/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.32/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.32/0.99      | ~ v1_funct_1(X2)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | v2_struct_0(X4)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ l1_pre_topc(X0)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X0) ),
% 2.32/0.99      inference(cnf_transformation,[],[f113]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_21,plain,
% 2.32/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.32/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.32/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.32/0.99      | ~ m1_pre_topc(X4,X0)
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.32/0.99      | ~ v1_funct_1(X2)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | v2_struct_0(X4)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ l1_pre_topc(X0)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X0) ),
% 2.32/0.99      inference(cnf_transformation,[],[f111]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_210,plain,
% 2.32/0.99      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.32/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.32/0.99      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.32/0.99      | ~ m1_pre_topc(X4,X0)
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.32/0.99      | ~ v1_funct_1(X2)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | v2_struct_0(X4)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ l1_pre_topc(X0)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X0) ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_23,c_21]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_211,plain,
% 2.32/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.32/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.32/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.32/0.99      | ~ m1_pre_topc(X4,X0)
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.32/0.99      | ~ v1_funct_1(X2)
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(X4)
% 2.32/0.99      | ~ l1_pre_topc(X0)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X0)
% 2.32/0.99      | ~ v2_pre_topc(X1) ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_210]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_645,plain,
% 2.32/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.32/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.32/0.99      | ~ m1_pre_topc(X4,X0)
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.32/0.99      | ~ v1_funct_1(X2)
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(X4)
% 2.32/0.99      | ~ l1_pre_topc(X0)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X0)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.32/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.32/0.99      | sK3 != X2 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_211,c_33]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_646,plain,
% 2.32/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.32/0.99      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.32/0.99      | ~ m1_pre_topc(X0,X2)
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.32/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.32/0.99      | ~ v1_funct_1(sK3)
% 2.32/0.99      | v2_struct_0(X2)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | ~ l1_pre_topc(X2)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X2)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.32/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_645]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_650,plain,
% 2.32/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_pre_topc(X0,X2)
% 2.32/0.99      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.32/0.99      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.32/0.99      | v2_struct_0(X2)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | ~ l1_pre_topc(X2)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X2)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.32/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_646,c_34]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_651,plain,
% 2.32/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.32/0.99      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.32/0.99      | ~ m1_pre_topc(X0,X2)
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.32/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(X2)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ l1_pre_topc(X2)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X2)
% 2.32/0.99      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.32/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_650]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_686,plain,
% 2.32/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.32/0.99      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.32/0.99      | ~ m1_pre_topc(X0,X2)
% 2.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | v2_struct_0(X1)
% 2.32/0.99      | v2_struct_0(X2)
% 2.32/0.99      | ~ l1_pre_topc(X1)
% 2.32/0.99      | ~ l1_pre_topc(X2)
% 2.32/0.99      | ~ v2_pre_topc(X1)
% 2.32/0.99      | ~ v2_pre_topc(X2)
% 2.32/0.99      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.32/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.32/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_651,c_9]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1984,plain,
% 2.32/0.99      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 2.32/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.32/0.99      | r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,sK3,X2),X3) = iProver_top
% 2.32/0.99      | r1_tmap_1(X0,X1,sK3,X3) != iProver_top
% 2.32/0.99      | m1_pre_topc(X2,X0) != iProver_top
% 2.32/0.99      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 2.32/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.32/0.99      | v2_struct_0(X1) = iProver_top
% 2.32/0.99      | v2_struct_0(X2) = iProver_top
% 2.32/0.99      | v2_struct_0(X0) = iProver_top
% 2.32/0.99      | l1_pre_topc(X1) != iProver_top
% 2.32/0.99      | l1_pre_topc(X0) != iProver_top
% 2.32/0.99      | v2_pre_topc(X1) != iProver_top
% 2.32/0.99      | v2_pre_topc(X0) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2793,plain,
% 2.32/0.99      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.32/0.99      | r1_tmap_1(X1,X0,k2_tmap_1(sK2,X0,sK3,X1),X2) = iProver_top
% 2.32/0.99      | r1_tmap_1(sK2,X0,sK3,X2) != iProver_top
% 2.32/0.99      | m1_pre_topc(X1,sK2) != iProver_top
% 2.32/0.99      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 2.32/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 2.32/0.99      | v2_struct_0(X1) = iProver_top
% 2.32/0.99      | v2_struct_0(X0) = iProver_top
% 2.32/0.99      | v2_struct_0(sK2) = iProver_top
% 2.32/0.99      | l1_pre_topc(X0) != iProver_top
% 2.32/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.32/0.99      | v2_pre_topc(X0) != iProver_top
% 2.32/0.99      | v2_pre_topc(sK2) != iProver_top ),
% 2.32/0.99      inference(equality_resolution,[status(thm)],[c_1984]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_44,plain,
% 2.32/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_45,plain,
% 2.32/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_46,plain,
% 2.32/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2798,plain,
% 2.32/0.99      ( v2_pre_topc(X0) != iProver_top
% 2.32/0.99      | v2_struct_0(X0) = iProver_top
% 2.32/0.99      | v2_struct_0(X1) = iProver_top
% 2.32/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 2.32/0.99      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 2.32/0.99      | m1_pre_topc(X1,sK2) != iProver_top
% 2.32/0.99      | r1_tmap_1(sK2,X0,sK3,X2) != iProver_top
% 2.32/0.99      | r1_tmap_1(X1,X0,k2_tmap_1(sK2,X0,sK3,X1),X2) = iProver_top
% 2.32/0.99      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.32/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_2793,c_44,c_45,c_46]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2799,plain,
% 2.32/0.99      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.32/0.99      | r1_tmap_1(X1,X0,k2_tmap_1(sK2,X0,sK3,X1),X2) = iProver_top
% 2.32/0.99      | r1_tmap_1(sK2,X0,sK3,X2) != iProver_top
% 2.32/0.99      | m1_pre_topc(X1,sK2) != iProver_top
% 2.32/0.99      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 2.32/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 2.32/0.99      | v2_struct_0(X1) = iProver_top
% 2.32/0.99      | v2_struct_0(X0) = iProver_top
% 2.32/0.99      | l1_pre_topc(X0) != iProver_top
% 2.32/0.99      | v2_pre_topc(X0) != iProver_top ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_2798]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2812,plain,
% 2.32/0.99      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK3,X0),X1) = iProver_top
% 2.32/0.99      | r1_tmap_1(sK2,sK1,sK3,X1) != iProver_top
% 2.32/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 2.32/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 2.32/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.32/0.99      | v2_struct_0(X0) = iProver_top
% 2.32/0.99      | v2_struct_0(sK1) = iProver_top
% 2.32/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.32/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 2.32/0.99      inference(equality_resolution,[status(thm)],[c_2799]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2866,plain,
% 2.32/0.99      ( v2_struct_0(X0) = iProver_top
% 2.32/0.99      | r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK3,X0),X1) = iProver_top
% 2.32/0.99      | r1_tmap_1(sK2,sK1,sK3,X1) != iProver_top
% 2.32/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 2.32/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_2812,c_41,c_42,c_43,c_49]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2867,plain,
% 2.32/0.99      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK3,X0),X1) = iProver_top
% 2.32/0.99      | r1_tmap_1(sK2,sK1,sK3,X1) != iProver_top
% 2.32/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 2.32/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 2.32/0.99      | v2_struct_0(X0) = iProver_top ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_2866]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_24,negated_conjecture,
% 2.32/0.99      ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
% 2.32/0.99      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 2.32/0.99      inference(cnf_transformation,[],[f105]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1998,plain,
% 2.32/0.99      ( r1_tmap_1(sK2,sK1,sK3,sK5) != iProver_top
% 2.32/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2067,plain,
% 2.32/0.99      ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
% 2.32/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
% 2.32/0.99      inference(light_normalisation,[status(thm)],[c_1998,c_26]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2877,plain,
% 2.32/0.99      ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
% 2.32/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.32/0.99      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 2.32/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_2867,c_2067]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2878,plain,
% 2.32/0.99      ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
% 2.32/0.99      | ~ m1_pre_topc(sK4,sK2)
% 2.32/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.32/0.99      | v2_struct_0(sK4) ),
% 2.32/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2877]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_7,plain,
% 2.32/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.32/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2593,plain,
% 2.32/0.99      ( ~ m1_pre_topc(sK4,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK4) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2595,plain,
% 2.32/0.99      ( ~ m1_pre_topc(sK4,sK2) | ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_2593]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1212,plain,
% 2.32/0.99      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/0.99      | v1_xboole_0(u1_struct_0(sK4))
% 2.32/0.99      | sP0_iProver_split ),
% 2.32/0.99      inference(splitting,
% 2.32/0.99                [splitting(split),new_symbols(definition,[])],
% 2.32/0.99                [c_971]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1981,plain,
% 2.32/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.32/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
% 2.32/0.99      | sP0_iProver_split = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_1212]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_52,plain,
% 2.32/0.99      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1242,plain,
% 2.32/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.32/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
% 2.32/0.99      | sP0_iProver_split = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_1212]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2332,plain,
% 2.32/0.99      ( ~ m1_pre_topc(sK4,sK2)
% 2.32/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/0.99      | ~ l1_pre_topc(sK2) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2333,plain,
% 2.32/0.99      ( m1_pre_topc(sK4,sK2) != iProver_top
% 2.32/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.32/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_2332]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2441,plain,
% 2.32/0.99      ( v1_xboole_0(u1_struct_0(sK4)) = iProver_top
% 2.32/0.99      | sP0_iProver_split = iProver_top ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_1981,c_46,c_52,c_1242,c_2333]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2443,plain,
% 2.32/0.99      ( v1_xboole_0(u1_struct_0(sK4)) | sP0_iProver_split ),
% 2.32/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2441]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_12,plain,
% 2.32/0.99      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.32/0.99      | v2_struct_0(X0)
% 2.32/0.99      | ~ l1_pre_topc(X0)
% 2.32/0.99      | ~ v2_pre_topc(X0) ),
% 2.32/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2425,plain,
% 2.32/0.99      ( m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.32/0.99      | v2_struct_0(sK4)
% 2.32/0.99      | ~ l1_pre_topc(sK4)
% 2.32/0.99      | ~ v2_pre_topc(sK4) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_27,negated_conjecture,
% 2.32/0.99      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.32/0.99      inference(cnf_transformation,[],[f102]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_31,negated_conjecture,
% 2.32/0.99      ( ~ v2_struct_0(sK4) ),
% 2.32/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(contradiction,plain,
% 2.32/0.99      ( $false ),
% 2.32/0.99      inference(minisat,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_3981,c_3368,c_3330,c_3093,c_2893,c_2878,c_2595,c_2443,
% 2.32/0.99                 c_2425,c_27,c_29,c_31,c_35,c_36]) ).
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.32/0.99  
% 2.32/0.99  ------                               Statistics
% 2.32/0.99  
% 2.32/0.99  ------ General
% 2.32/0.99  
% 2.32/0.99  abstr_ref_over_cycles:                  0
% 2.32/0.99  abstr_ref_under_cycles:                 0
% 2.32/0.99  gc_basic_clause_elim:                   0
% 2.32/0.99  forced_gc_time:                         0
% 2.32/0.99  parsing_time:                           0.01
% 2.32/0.99  unif_index_cands_time:                  0.
% 2.32/0.99  unif_index_add_time:                    0.
% 2.32/0.99  orderings_time:                         0.
% 2.32/0.99  out_proof_time:                         0.021
% 2.32/0.99  total_time:                             0.188
% 2.32/0.99  num_of_symbols:                         57
% 2.32/0.99  num_of_terms:                           2355
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing
% 2.32/0.99  
% 2.32/0.99  num_of_splits:                          1
% 2.32/0.99  num_of_split_atoms:                     1
% 2.32/0.99  num_of_reused_defs:                     0
% 2.32/0.99  num_eq_ax_congr_red:                    9
% 2.32/0.99  num_of_sem_filtered_clauses:            1
% 2.32/0.99  num_of_subtypes:                        0
% 2.32/0.99  monotx_restored_types:                  0
% 2.32/0.99  sat_num_of_epr_types:                   0
% 2.32/0.99  sat_num_of_non_cyclic_types:            0
% 2.32/0.99  sat_guarded_non_collapsed_types:        0
% 2.32/0.99  num_pure_diseq_elim:                    0
% 2.32/0.99  simp_replaced_by:                       0
% 2.32/0.99  res_preprocessed:                       160
% 2.32/0.99  prep_upred:                             0
% 2.32/0.99  prep_unflattend:                        23
% 2.32/0.99  smt_new_axioms:                         0
% 2.32/0.99  pred_elim_cands:                        8
% 2.32/0.99  pred_elim:                              6
% 2.32/0.99  pred_elim_cl:                           9
% 2.32/0.99  pred_elim_cycles:                       8
% 2.32/0.99  merged_defs:                            8
% 2.32/0.99  merged_defs_ncl:                        0
% 2.32/0.99  bin_hyper_res:                          8
% 2.32/0.99  prep_cycles:                            4
% 2.32/0.99  pred_elim_time:                         0.017
% 2.32/0.99  splitting_time:                         0.
% 2.32/0.99  sem_filter_time:                        0.
% 2.32/0.99  monotx_time:                            0.
% 2.32/0.99  subtype_inf_time:                       0.
% 2.32/0.99  
% 2.32/0.99  ------ Problem properties
% 2.32/0.99  
% 2.32/0.99  clauses:                                31
% 2.32/0.99  conjectures:                            14
% 2.32/0.99  epr:                                    13
% 2.32/0.99  horn:                                   23
% 2.32/0.99  ground:                                 15
% 2.32/0.99  unary:                                  13
% 2.32/0.99  binary:                                 2
% 2.32/0.99  lits:                                   113
% 2.32/0.99  lits_eq:                                7
% 2.32/0.99  fd_pure:                                0
% 2.32/0.99  fd_pseudo:                              0
% 2.32/0.99  fd_cond:                                0
% 2.32/0.99  fd_pseudo_cond:                         1
% 2.32/0.99  ac_symbols:                             0
% 2.32/0.99  
% 2.32/0.99  ------ Propositional Solver
% 2.32/0.99  
% 2.32/0.99  prop_solver_calls:                      26
% 2.32/0.99  prop_fast_solver_calls:                 1621
% 2.32/0.99  smt_solver_calls:                       0
% 2.32/0.99  smt_fast_solver_calls:                  0
% 2.32/0.99  prop_num_of_clauses:                    952
% 2.32/0.99  prop_preprocess_simplified:             4998
% 2.32/0.99  prop_fo_subsumed:                       56
% 2.32/0.99  prop_solver_time:                       0.
% 2.32/0.99  smt_solver_time:                        0.
% 2.32/0.99  smt_fast_solver_time:                   0.
% 2.32/0.99  prop_fast_solver_time:                  0.
% 2.32/0.99  prop_unsat_core_time:                   0.
% 2.32/0.99  
% 2.32/0.99  ------ QBF
% 2.32/0.99  
% 2.32/0.99  qbf_q_res:                              0
% 2.32/0.99  qbf_num_tautologies:                    0
% 2.32/0.99  qbf_prep_cycles:                        0
% 2.32/0.99  
% 2.32/0.99  ------ BMC1
% 2.32/0.99  
% 2.32/0.99  bmc1_current_bound:                     -1
% 2.32/0.99  bmc1_last_solved_bound:                 -1
% 2.32/0.99  bmc1_unsat_core_size:                   -1
% 2.32/0.99  bmc1_unsat_core_parents_size:           -1
% 2.32/0.99  bmc1_merge_next_fun:                    0
% 2.32/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.32/0.99  
% 2.32/0.99  ------ Instantiation
% 2.32/0.99  
% 2.32/0.99  inst_num_of_clauses:                    290
% 2.32/0.99  inst_num_in_passive:                    80
% 2.32/0.99  inst_num_in_active:                     200
% 2.32/0.99  inst_num_in_unprocessed:                9
% 2.32/0.99  inst_num_of_loops:                      211
% 2.32/0.99  inst_num_of_learning_restarts:          0
% 2.32/0.99  inst_num_moves_active_passive:          7
% 2.32/0.99  inst_lit_activity:                      0
% 2.32/0.99  inst_lit_activity_moves:                0
% 2.32/0.99  inst_num_tautologies:                   0
% 2.32/0.99  inst_num_prop_implied:                  0
% 2.32/0.99  inst_num_existing_simplified:           0
% 2.32/0.99  inst_num_eq_res_simplified:             0
% 2.32/0.99  inst_num_child_elim:                    0
% 2.32/0.99  inst_num_of_dismatching_blockings:      34
% 2.32/0.99  inst_num_of_non_proper_insts:           308
% 2.32/0.99  inst_num_of_duplicates:                 0
% 2.32/0.99  inst_inst_num_from_inst_to_res:         0
% 2.32/0.99  inst_dismatching_checking_time:         0.
% 2.32/0.99  
% 2.32/0.99  ------ Resolution
% 2.32/0.99  
% 2.32/0.99  res_num_of_clauses:                     0
% 2.32/0.99  res_num_in_passive:                     0
% 2.32/0.99  res_num_in_active:                      0
% 2.32/0.99  res_num_of_loops:                       164
% 2.32/0.99  res_forward_subset_subsumed:            60
% 2.32/0.99  res_backward_subset_subsumed:           0
% 2.32/0.99  res_forward_subsumed:                   1
% 2.32/0.99  res_backward_subsumed:                  0
% 2.32/0.99  res_forward_subsumption_resolution:     4
% 2.32/0.99  res_backward_subsumption_resolution:    0
% 2.32/0.99  res_clause_to_clause_subsumption:       168
% 2.32/0.99  res_orphan_elimination:                 0
% 2.32/0.99  res_tautology_del:                      62
% 2.32/0.99  res_num_eq_res_simplified:              1
% 2.32/0.99  res_num_sel_changes:                    0
% 2.32/0.99  res_moves_from_active_to_pass:          0
% 2.32/0.99  
% 2.32/0.99  ------ Superposition
% 2.32/0.99  
% 2.32/0.99  sup_time_total:                         0.
% 2.32/0.99  sup_time_generating:                    0.
% 2.32/0.99  sup_time_sim_full:                      0.
% 2.32/0.99  sup_time_sim_immed:                     0.
% 2.32/0.99  
% 2.32/0.99  sup_num_of_clauses:                     49
% 2.32/0.99  sup_num_in_active:                      40
% 2.32/0.99  sup_num_in_passive:                     9
% 2.32/0.99  sup_num_of_loops:                       42
% 2.32/0.99  sup_fw_superposition:                   13
% 2.32/0.99  sup_bw_superposition:                   5
% 2.32/0.99  sup_immediate_simplified:               0
% 2.32/0.99  sup_given_eliminated:                   0
% 2.32/0.99  comparisons_done:                       0
% 2.32/0.99  comparisons_avoided:                    0
% 2.32/0.99  
% 2.32/0.99  ------ Simplifications
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  sim_fw_subset_subsumed:                 0
% 2.32/0.99  sim_bw_subset_subsumed:                 3
% 2.32/0.99  sim_fw_subsumed:                        0
% 2.32/0.99  sim_bw_subsumed:                        0
% 2.32/0.99  sim_fw_subsumption_res:                 0
% 2.32/0.99  sim_bw_subsumption_res:                 0
% 2.32/0.99  sim_tautology_del:                      3
% 2.32/0.99  sim_eq_tautology_del:                   1
% 2.32/0.99  sim_eq_res_simp:                        0
% 2.32/0.99  sim_fw_demodulated:                     0
% 2.32/0.99  sim_bw_demodulated:                     0
% 2.32/0.99  sim_light_normalised:                   3
% 2.32/0.99  sim_joinable_taut:                      0
% 2.32/0.99  sim_joinable_simp:                      0
% 2.32/0.99  sim_ac_normalised:                      0
% 2.32/0.99  sim_smt_subsumption:                    0
% 2.32/0.99  
%------------------------------------------------------------------------------
