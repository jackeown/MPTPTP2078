%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:43 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :  277 (1406 expanded)
%              Number of clauses        :  179 ( 262 expanded)
%              Number of leaves         :   23 ( 540 expanded)
%              Depth                    :   33
%              Number of atoms          : 1821 (21498 expanded)
%              Number of equality atoms :  227 (1595 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_connsp_2(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X3) )
     => ( r1_tarski(sK1(X0,X1,X2),X2)
        & v3_pre_topc(sK1(X0,X1,X2),X0)
        & m1_connsp_2(sK1(X0,X1,X2),X0,X1)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(sK1(X0,X1,X2),X2)
                & v3_pre_topc(sK1(X0,X1,X2),X0)
                & m1_connsp_2(sK1(X0,X1,X2),X0,X1)
                & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(sK1(X0,X1,X2)) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f46])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK1(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | ~ r1_tmap_1(X1,X0,X2,X4) )
          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | r1_tmap_1(X1,X0,X2,X4) )
          & X4 = X5
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7)
          | ~ r1_tmap_1(X1,X0,X2,X4) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7)
          | r1_tmap_1(X1,X0,X2,X4) )
        & sK7 = X4
        & m1_subset_1(sK7,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
              | ~ r1_tmap_1(X1,X0,X2,sK6) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | r1_tmap_1(X1,X0,X2,sK6) )
            & sK6 = X5
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_subset_1(sK6,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
                ( ( ~ r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5)
                  | ~ r1_tmap_1(X1,X0,X2,X4) )
                & ( r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5)
                  | r1_tmap_1(X1,X0,X2,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(sK5)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_pre_topc(sK5,X1)
        & v1_tsep_1(sK5,X1)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
                    ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5)
                      | ~ r1_tmap_1(X1,X0,sK4,X4) )
                    & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5)
                      | r1_tmap_1(X1,X0,sK4,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_pre_topc(X3,X1)
            & v1_tsep_1(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
                        ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5)
                          | ~ r1_tmap_1(sK3,X0,X2,X4) )
                        & ( r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5)
                          | r1_tmap_1(sK3,X0,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(sK3)) )
                & m1_pre_topc(X3,sK3)
                & v1_tsep_1(X3,sK3)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
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
                          ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK2,X2,X4) )
                          & ( r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5)
                            | r1_tmap_1(X1,sK2,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
      | ~ r1_tmap_1(sK3,sK2,sK4,sK6) )
    & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
      | r1_tmap_1(sK3,sK2,sK4,sK6) )
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_pre_topc(sK5,sK3)
    & v1_tsep_1(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f52,f58,f57,f56,f55,f54,f53])).

fof(f85,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f84,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f86,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f96,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | r1_tmap_1(sK3,sK2,sK4,sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f59])).

fof(f92,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f59])).

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
                                  & r1_tarski(X4,u1_struct_0(X3))
                                  & r2_hidden(X5,X4)
                                  & v3_pre_topc(X4,X1) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f102,plain,(
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
    inference(equality_resolution,[],[f80])).

fof(f88,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f59])).

fof(f87,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(flattening,[],[f23])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f90,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f82,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f81,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f83,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f94,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f59])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f103,plain,(
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
    inference(equality_resolution,[],[f79])).

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

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f101,plain,(
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
    inference(equality_resolution,[],[f78])).

fof(f97,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ r1_tmap_1(sK3,sK2,sK4,sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK0(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f44])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f91,plain,(
    v1_tsep_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_5,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_5])).

cnf(c_237,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_236])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1784,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_237,c_33])).

cnf(c_1785,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | m1_connsp_2(sK1(sK3,X1,X0),sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1784])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1789,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | m1_connsp_2(sK1(sK3,X1,X0),sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1785,c_34,c_32])).

cnf(c_4611,plain,
    ( ~ m1_connsp_2(X0_54,sK3,X1_54)
    | m1_connsp_2(sK1(sK3,X1_54,X0_54),sK3,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1789])).

cnf(c_5745,plain,
    ( m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
    | m1_connsp_2(sK1(sK3,X1_54,X0_54),sK3,X1_54) = iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4611])).

cnf(c_8,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_257,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_5])).

cnf(c_258,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_257])).

cnf(c_1721,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_258,c_33])).

cnf(c_1722,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1721])).

cnf(c_1726,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1722,c_34,c_32])).

cnf(c_4614,plain,
    ( ~ m1_connsp_2(X0_54,sK3,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | r2_hidden(X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_1726])).

cnf(c_5742,plain,
    ( m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1_54,X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4614])).

cnf(c_7425,plain,
    ( m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1_54,sK1(sK3,X1_54,X0_54)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5745,c_5742])).

cnf(c_9,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_250,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_5])).

cnf(c_251,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_250])).

cnf(c_1742,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_251,c_33])).

cnf(c_1743,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | r1_tarski(sK1(sK3,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1742])).

cnf(c_1747,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | r1_tarski(sK1(sK3,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1743,c_34,c_32])).

cnf(c_4613,plain,
    ( ~ m1_connsp_2(X0_54,sK3,X1_54)
    | r1_tarski(sK1(sK3,X1_54,X0_54),X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1747])).

cnf(c_5743,plain,
    ( m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
    | r1_tarski(sK1(sK3,X1_54,X0_54),X0_54) = iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4613])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_5])).

cnf(c_230,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_229])).

cnf(c_1805,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_230,c_33])).

cnf(c_1806,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1805])).

cnf(c_1810,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1806,c_34,c_32])).

cnf(c_4610,plain,
    ( ~ m1_connsp_2(X0_54,sK3,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X1_54,X0_54),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1810])).

cnf(c_5746,plain,
    ( m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,X1_54,X0_54),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4610])).

cnf(c_22,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK6)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_4631,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK6)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_5722,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK6) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4631])).

cnf(c_23,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_4630,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_5801,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5722,c_4630])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_19,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v3_pre_topc(X5,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_690,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v3_pre_topc(X5,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_691,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v3_pre_topc(X4,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r2_hidden(X3,X4)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_690])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_695,plain,
    ( ~ r2_hidden(X3,X4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ v3_pre_topc(X4,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_691,c_31])).

cnf(c_696,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v3_pre_topc(X4,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r2_hidden(X3,X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_695])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_739,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v3_pre_topc(X4,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r2_hidden(X3,X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_696,c_4])).

cnf(c_911,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v3_pre_topc(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r2_hidden(X3,X4)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_739])).

cnf(c_912,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X1,X2)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_911])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_916,plain,
    ( ~ v2_pre_topc(X0)
    | r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X1,X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_912,c_34,c_33,c_32,c_28])).

cnf(c_917,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X1,X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_916])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1583,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X1,X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_917,c_36])).

cnf(c_1584,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | ~ v3_pre_topc(X1,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ r2_hidden(X0,X1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1583])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1588,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v3_pre_topc(X1,sK3)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r2_hidden(X0,X1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1584,c_37,c_35,c_29])).

cnf(c_1589,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | ~ v3_pre_topc(X1,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1588])).

cnf(c_4619,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_54)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
    | ~ r1_tarski(X1_54,u1_struct_0(sK5))
    | ~ v3_pre_topc(X1_54,sK3)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0_54,X1_54)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_1589])).

cnf(c_5735,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | r1_tmap_1(sK3,sK2,sK4,X0_54) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54) != iProver_top
    | r1_tarski(X1_54,u1_struct_0(sK5)) != iProver_top
    | v3_pre_topc(X1_54,sK3) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0_54,X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4619])).

cnf(c_6052,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_54) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54) != iProver_top
    | r1_tarski(X1_54,u1_struct_0(sK5)) != iProver_top
    | v3_pre_topc(X1_54,sK3) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0_54,X1_54) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5735])).

cnf(c_9184,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
    | r1_tarski(X0_54,u1_struct_0(sK5)) != iProver_top
    | v3_pre_topc(X0_54,sK3) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK7,X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_5801,c_6052])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_51,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_20,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v3_pre_topc(X5,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f101])).

cnf(c_200,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_18])).

cnf(c_201,plain,
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
    inference(renaming,[status(thm)],[c_200])).

cnf(c_633,plain,
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
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_201,c_30])).

cnf(c_634,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_633])).

cnf(c_638,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_634,c_31])).

cnf(c_639,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_638])).

cnf(c_674,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_639,c_4])).

cnf(c_962,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_674])).

cnf(c_963,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_962])).

cnf(c_967,plain,
    ( ~ v2_pre_topc(X0)
    | ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_963,c_34,c_33,c_32,c_28])).

cnf(c_968,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_967])).

cnf(c_1559,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_968,c_36])).

cnf(c_1560,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1559])).

cnf(c_1564,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1560,c_37,c_35,c_29])).

cnf(c_1565,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1564])).

cnf(c_4620,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0_54)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_1565])).

cnf(c_5734,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | r1_tmap_1(sK3,sK2,sK4,X0_54) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4620])).

cnf(c_5983,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_54) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5734])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_4632,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_5721,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK6) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4632])).

cnf(c_5812,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5721,c_4630])).

cnf(c_8575,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5983,c_5812])).

cnf(c_9275,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(X0_54,sK3) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK7,X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9184,c_51,c_8575])).

cnf(c_9276,plain,
    ( r1_tarski(X0_54,u1_struct_0(sK5)) != iProver_top
    | v3_pre_topc(X0_54,sK3) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK7,X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_9275])).

cnf(c_9286,plain,
    ( m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
    | r1_tarski(sK1(sK3,X1_54,X0_54),u1_struct_0(sK5)) != iProver_top
    | v3_pre_topc(sK1(sK3,X1_54,X0_54),sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK7,sK1(sK3,X1_54,X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5746,c_9276])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_243,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_5])).

cnf(c_244,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_243])).

cnf(c_1763,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_244,c_33])).

cnf(c_1764,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | v3_pre_topc(sK1(sK3,X1,X0),sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1763])).

cnf(c_1768,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | v3_pre_topc(sK1(sK3,X1,X0),sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1764,c_34,c_32])).

cnf(c_4612,plain,
    ( ~ m1_connsp_2(X0_54,sK3,X1_54)
    | v3_pre_topc(sK1(sK3,X1_54,X0_54),sK3)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1768])).

cnf(c_4719,plain,
    ( m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
    | v3_pre_topc(sK1(sK3,X1_54,X0_54),sK3) = iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4612])).

cnf(c_9505,plain,
    ( r1_tarski(sK1(sK3,X1_54,X0_54),u1_struct_0(sK5)) != iProver_top
    | m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK7,sK1(sK3,X1_54,X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9286,c_4719])).

cnf(c_9506,plain,
    ( m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
    | r1_tarski(sK1(sK3,X1_54,X0_54),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK7,sK1(sK3,X1_54,X0_54)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9505])).

cnf(c_9515,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,X0_54) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK7,sK1(sK3,X0_54,u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5743,c_9506])).

cnf(c_9523,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7425,c_9515])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_4633,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ r2_hidden(X2_54,X0_54)
    | ~ v1_xboole_0(X1_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_6435,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1_54,X0_54)
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4633])).

cnf(c_6758,plain,
    ( ~ m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0_54,sK0(sK5,sK7))
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6435])).

cnf(c_7722,plain,
    ( ~ m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK7,sK0(sK5,sK7))
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6758])).

cnf(c_7723,plain,
    ( m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK7,sK0(sK5,sK7)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7722])).

cnf(c_7,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1847,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_33])).

cnf(c_1848,plain,
    ( m1_connsp_2(X0,sK3,X1)
    | ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1847])).

cnf(c_1852,plain,
    ( m1_connsp_2(X0,sK3,X1)
    | ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1848,c_34,c_32])).

cnf(c_4608,plain,
    ( m1_connsp_2(X0_54,sK3,X1_54)
    | ~ v3_pre_topc(X0_54,sK3)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_1852])).

cnf(c_6223,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,X0_54)
    | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0_54,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4608])).

cnf(c_6752,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
    | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6223])).

cnf(c_6753,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7) = iProver_top
    | v3_pre_topc(u1_struct_0(sK5),sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6752])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_900,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK3 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_26])).

cnf(c_901,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_900])).

cnf(c_903,plain,
    ( v2_pre_topc(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_901,c_33,c_32])).

cnf(c_2069,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_258,c_903])).

cnf(c_2070,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,X0)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_2069])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_889,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_26])).

cnf(c_890,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_2074,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2070,c_32,c_28,c_890])).

cnf(c_4598,plain,
    ( ~ m1_connsp_2(X0_54,sK5,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
    | r2_hidden(X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_2074])).

cnf(c_6258,plain,
    ( ~ m1_connsp_2(X0_54,sK5,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | r2_hidden(sK7,X0_54) ),
    inference(instantiation,[status(thm)],[c_4598])).

cnf(c_6504,plain,
    ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | r2_hidden(sK7,sK0(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_6258])).

cnf(c_6505,plain,
    ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK7,sK0(sK5,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6504])).

cnf(c_2222,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_903])).

cnf(c_2223,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_2222])).

cnf(c_2227,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2223,c_32,c_28,c_890])).

cnf(c_4591,plain,
    ( ~ m1_connsp_2(X0_54,sK5,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_2227])).

cnf(c_6234,plain,
    ( ~ m1_connsp_2(X0_54,sK5,sK7)
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4591])).

cnf(c_6492,plain,
    ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
    | m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6234])).

cnf(c_6493,plain,
    ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) != iProver_top
    | m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6492])).

cnf(c_4629,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_5723,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4629])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_4634,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | r2_hidden(X0_54,X1_54)
    | v1_xboole_0(X1_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_5719,plain,
    ( m1_subset_1(X0_54,X1_54) != iProver_top
    | r2_hidden(X0_54,X1_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4634])).

cnf(c_6282,plain,
    ( r2_hidden(sK7,u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5723,c_5719])).

cnf(c_6,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1703,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_903])).

cnf(c_1704,plain,
    ( m1_connsp_2(sK0(sK5,X0),sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_1703])).

cnf(c_1708,plain,
    ( m1_connsp_2(sK0(sK5,X0),sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1704,c_32,c_28,c_890])).

cnf(c_4615,plain,
    ( m1_connsp_2(sK0(sK5,X0_54),sK5,X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_1708])).

cnf(c_6228,plain,
    ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4615])).

cnf(c_6229,plain,
    ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6228])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_4628,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_5724,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4628])).

cnf(c_5770,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5724,c_4630])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_860,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_861,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_860])).

cnf(c_862,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_861])).

cnf(c_16,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_208,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_17])).

cnf(c_209,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_27,negated_conjecture,
    ( v1_tsep_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_567,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_209,c_27])).

cnf(c_568,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ m1_pre_topc(sK5,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_569,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK3) = iProver_top
    | m1_pre_topc(sK5,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_568])).

cnf(c_49,plain,
    ( m1_pre_topc(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_43,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9523,c_7723,c_6753,c_6505,c_6493,c_6282,c_6229,c_5770,c_862,c_569,c_51,c_49,c_43,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 19:51:49 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 2.50/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/0.97  
% 2.50/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.50/0.97  
% 2.50/0.97  ------  iProver source info
% 2.50/0.97  
% 2.50/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.50/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.50/0.97  git: non_committed_changes: false
% 2.50/0.97  git: last_make_outside_of_git: false
% 2.50/0.97  
% 2.50/0.97  ------ 
% 2.50/0.97  
% 2.50/0.97  ------ Input Options
% 2.50/0.97  
% 2.50/0.97  --out_options                           all
% 2.50/0.97  --tptp_safe_out                         true
% 2.50/0.97  --problem_path                          ""
% 2.50/0.97  --include_path                          ""
% 2.50/0.97  --clausifier                            res/vclausify_rel
% 2.50/0.97  --clausifier_options                    --mode clausify
% 2.50/0.97  --stdin                                 false
% 2.50/0.97  --stats_out                             all
% 2.50/0.97  
% 2.50/0.97  ------ General Options
% 2.50/0.97  
% 2.50/0.97  --fof                                   false
% 2.50/0.97  --time_out_real                         305.
% 2.50/0.97  --time_out_virtual                      -1.
% 2.50/0.97  --symbol_type_check                     false
% 2.50/0.97  --clausify_out                          false
% 2.50/0.97  --sig_cnt_out                           false
% 2.50/0.97  --trig_cnt_out                          false
% 2.50/0.97  --trig_cnt_out_tolerance                1.
% 2.50/0.97  --trig_cnt_out_sk_spl                   false
% 2.50/0.97  --abstr_cl_out                          false
% 2.50/0.97  
% 2.50/0.97  ------ Global Options
% 2.50/0.97  
% 2.50/0.97  --schedule                              default
% 2.50/0.97  --add_important_lit                     false
% 2.50/0.97  --prop_solver_per_cl                    1000
% 2.50/0.97  --min_unsat_core                        false
% 2.50/0.97  --soft_assumptions                      false
% 2.50/0.97  --soft_lemma_size                       3
% 2.50/0.97  --prop_impl_unit_size                   0
% 2.50/0.97  --prop_impl_unit                        []
% 2.50/0.97  --share_sel_clauses                     true
% 2.50/0.97  --reset_solvers                         false
% 2.50/0.97  --bc_imp_inh                            [conj_cone]
% 2.50/0.97  --conj_cone_tolerance                   3.
% 2.50/0.97  --extra_neg_conj                        none
% 2.50/0.97  --large_theory_mode                     true
% 2.50/0.97  --prolific_symb_bound                   200
% 2.50/0.97  --lt_threshold                          2000
% 2.50/0.97  --clause_weak_htbl                      true
% 2.50/0.97  --gc_record_bc_elim                     false
% 2.50/0.97  
% 2.50/0.97  ------ Preprocessing Options
% 2.50/0.97  
% 2.50/0.97  --preprocessing_flag                    true
% 2.50/0.97  --time_out_prep_mult                    0.1
% 2.50/0.97  --splitting_mode                        input
% 2.50/0.97  --splitting_grd                         true
% 2.50/0.97  --splitting_cvd                         false
% 2.50/0.97  --splitting_cvd_svl                     false
% 2.50/0.97  --splitting_nvd                         32
% 2.50/0.97  --sub_typing                            true
% 2.50/0.97  --prep_gs_sim                           true
% 2.50/0.97  --prep_unflatten                        true
% 2.50/0.97  --prep_res_sim                          true
% 2.50/0.97  --prep_upred                            true
% 2.50/0.97  --prep_sem_filter                       exhaustive
% 2.50/0.97  --prep_sem_filter_out                   false
% 2.50/0.97  --pred_elim                             true
% 2.50/0.97  --res_sim_input                         true
% 2.50/0.97  --eq_ax_congr_red                       true
% 2.50/0.97  --pure_diseq_elim                       true
% 2.50/0.97  --brand_transform                       false
% 2.50/0.97  --non_eq_to_eq                          false
% 2.50/0.97  --prep_def_merge                        true
% 2.50/0.97  --prep_def_merge_prop_impl              false
% 2.50/0.97  --prep_def_merge_mbd                    true
% 2.50/0.97  --prep_def_merge_tr_red                 false
% 2.50/0.97  --prep_def_merge_tr_cl                  false
% 2.50/0.97  --smt_preprocessing                     true
% 2.50/0.97  --smt_ac_axioms                         fast
% 2.50/0.97  --preprocessed_out                      false
% 2.50/0.97  --preprocessed_stats                    false
% 2.50/0.97  
% 2.50/0.97  ------ Abstraction refinement Options
% 2.50/0.97  
% 2.50/0.97  --abstr_ref                             []
% 2.50/0.97  --abstr_ref_prep                        false
% 2.50/0.97  --abstr_ref_until_sat                   false
% 2.50/0.97  --abstr_ref_sig_restrict                funpre
% 2.50/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/0.97  --abstr_ref_under                       []
% 2.50/0.97  
% 2.50/0.97  ------ SAT Options
% 2.50/0.97  
% 2.50/0.97  --sat_mode                              false
% 2.50/0.97  --sat_fm_restart_options                ""
% 2.50/0.97  --sat_gr_def                            false
% 2.50/0.97  --sat_epr_types                         true
% 2.50/0.97  --sat_non_cyclic_types                  false
% 2.50/0.97  --sat_finite_models                     false
% 2.50/0.97  --sat_fm_lemmas                         false
% 2.50/0.97  --sat_fm_prep                           false
% 2.50/0.97  --sat_fm_uc_incr                        true
% 2.50/0.97  --sat_out_model                         small
% 2.50/0.97  --sat_out_clauses                       false
% 2.50/0.97  
% 2.50/0.97  ------ QBF Options
% 2.50/0.97  
% 2.50/0.97  --qbf_mode                              false
% 2.50/0.97  --qbf_elim_univ                         false
% 2.50/0.97  --qbf_dom_inst                          none
% 2.50/0.97  --qbf_dom_pre_inst                      false
% 2.50/0.97  --qbf_sk_in                             false
% 2.50/0.97  --qbf_pred_elim                         true
% 2.50/0.97  --qbf_split                             512
% 2.50/0.97  
% 2.50/0.97  ------ BMC1 Options
% 2.50/0.97  
% 2.50/0.97  --bmc1_incremental                      false
% 2.50/0.97  --bmc1_axioms                           reachable_all
% 2.50/0.97  --bmc1_min_bound                        0
% 2.50/0.97  --bmc1_max_bound                        -1
% 2.50/0.97  --bmc1_max_bound_default                -1
% 2.50/0.97  --bmc1_symbol_reachability              true
% 2.50/0.97  --bmc1_property_lemmas                  false
% 2.50/0.97  --bmc1_k_induction                      false
% 2.50/0.97  --bmc1_non_equiv_states                 false
% 2.50/0.97  --bmc1_deadlock                         false
% 2.50/0.97  --bmc1_ucm                              false
% 2.50/0.97  --bmc1_add_unsat_core                   none
% 2.50/0.97  --bmc1_unsat_core_children              false
% 2.50/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/0.97  --bmc1_out_stat                         full
% 2.50/0.97  --bmc1_ground_init                      false
% 2.50/0.97  --bmc1_pre_inst_next_state              false
% 2.50/0.97  --bmc1_pre_inst_state                   false
% 2.50/0.97  --bmc1_pre_inst_reach_state             false
% 2.50/0.97  --bmc1_out_unsat_core                   false
% 2.50/0.97  --bmc1_aig_witness_out                  false
% 2.50/0.97  --bmc1_verbose                          false
% 2.50/0.97  --bmc1_dump_clauses_tptp                false
% 2.50/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.50/0.97  --bmc1_dump_file                        -
% 2.50/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.50/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.50/0.97  --bmc1_ucm_extend_mode                  1
% 2.50/0.97  --bmc1_ucm_init_mode                    2
% 2.50/0.97  --bmc1_ucm_cone_mode                    none
% 2.50/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.50/0.97  --bmc1_ucm_relax_model                  4
% 2.50/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.50/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/0.97  --bmc1_ucm_layered_model                none
% 2.50/0.97  --bmc1_ucm_max_lemma_size               10
% 2.50/0.97  
% 2.50/0.97  ------ AIG Options
% 2.50/0.97  
% 2.50/0.97  --aig_mode                              false
% 2.50/0.97  
% 2.50/0.97  ------ Instantiation Options
% 2.50/0.97  
% 2.50/0.97  --instantiation_flag                    true
% 2.50/0.97  --inst_sos_flag                         false
% 2.50/0.97  --inst_sos_phase                        true
% 2.50/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/0.97  --inst_lit_sel_side                     num_symb
% 2.50/0.97  --inst_solver_per_active                1400
% 2.50/0.97  --inst_solver_calls_frac                1.
% 2.50/0.97  --inst_passive_queue_type               priority_queues
% 2.50/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/0.97  --inst_passive_queues_freq              [25;2]
% 2.50/0.97  --inst_dismatching                      true
% 2.50/0.97  --inst_eager_unprocessed_to_passive     true
% 2.50/0.97  --inst_prop_sim_given                   true
% 2.50/0.97  --inst_prop_sim_new                     false
% 2.50/0.97  --inst_subs_new                         false
% 2.50/0.97  --inst_eq_res_simp                      false
% 2.50/0.97  --inst_subs_given                       false
% 2.50/0.97  --inst_orphan_elimination               true
% 2.50/0.97  --inst_learning_loop_flag               true
% 2.50/0.97  --inst_learning_start                   3000
% 2.50/0.97  --inst_learning_factor                  2
% 2.50/0.97  --inst_start_prop_sim_after_learn       3
% 2.50/0.97  --inst_sel_renew                        solver
% 2.50/0.97  --inst_lit_activity_flag                true
% 2.50/0.97  --inst_restr_to_given                   false
% 2.50/0.97  --inst_activity_threshold               500
% 2.50/0.97  --inst_out_proof                        true
% 2.50/0.97  
% 2.50/0.97  ------ Resolution Options
% 2.50/0.97  
% 2.50/0.97  --resolution_flag                       true
% 2.50/0.97  --res_lit_sel                           adaptive
% 2.50/0.97  --res_lit_sel_side                      none
% 2.50/0.97  --res_ordering                          kbo
% 2.50/0.97  --res_to_prop_solver                    active
% 2.50/0.97  --res_prop_simpl_new                    false
% 2.50/0.97  --res_prop_simpl_given                  true
% 2.50/0.97  --res_passive_queue_type                priority_queues
% 2.50/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/0.97  --res_passive_queues_freq               [15;5]
% 2.50/0.97  --res_forward_subs                      full
% 2.50/0.97  --res_backward_subs                     full
% 2.50/0.97  --res_forward_subs_resolution           true
% 2.50/0.97  --res_backward_subs_resolution          true
% 2.50/0.97  --res_orphan_elimination                true
% 2.50/0.97  --res_time_limit                        2.
% 2.50/0.97  --res_out_proof                         true
% 2.50/0.97  
% 2.50/0.97  ------ Superposition Options
% 2.50/0.97  
% 2.50/0.97  --superposition_flag                    true
% 2.50/0.97  --sup_passive_queue_type                priority_queues
% 2.50/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.50/0.97  --demod_completeness_check              fast
% 2.50/0.97  --demod_use_ground                      true
% 2.50/0.97  --sup_to_prop_solver                    passive
% 2.50/0.97  --sup_prop_simpl_new                    true
% 2.50/0.97  --sup_prop_simpl_given                  true
% 2.50/0.97  --sup_fun_splitting                     false
% 2.50/0.97  --sup_smt_interval                      50000
% 2.50/0.97  
% 2.50/0.97  ------ Superposition Simplification Setup
% 2.50/0.97  
% 2.50/0.97  --sup_indices_passive                   []
% 2.50/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.97  --sup_full_bw                           [BwDemod]
% 2.50/0.97  --sup_immed_triv                        [TrivRules]
% 2.50/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.97  --sup_immed_bw_main                     []
% 2.50/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.97  
% 2.50/0.97  ------ Combination Options
% 2.50/0.97  
% 2.50/0.97  --comb_res_mult                         3
% 2.50/0.97  --comb_sup_mult                         2
% 2.50/0.97  --comb_inst_mult                        10
% 2.50/0.97  
% 2.50/0.97  ------ Debug Options
% 2.50/0.97  
% 2.50/0.97  --dbg_backtrace                         false
% 2.50/0.97  --dbg_dump_prop_clauses                 false
% 2.50/0.97  --dbg_dump_prop_clauses_file            -
% 2.50/0.97  --dbg_out_stat                          false
% 2.50/0.97  ------ Parsing...
% 2.50/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.50/0.97  
% 2.50/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 2.50/0.97  
% 2.50/0.97  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.50/0.97  
% 2.50/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.50/0.97  ------ Proving...
% 2.50/0.97  ------ Problem Properties 
% 2.50/0.97  
% 2.50/0.97  
% 2.50/0.97  clauses                                 48
% 2.50/0.97  conjectures                             6
% 2.50/0.97  EPR                                     2
% 2.50/0.97  Horn                                    46
% 2.50/0.97  unary                                   6
% 2.50/0.97  binary                                  6
% 2.50/0.97  lits                                    150
% 2.50/0.97  lits eq                                 7
% 2.50/0.97  fd_pure                                 0
% 2.50/0.97  fd_pseudo                               0
% 2.50/0.97  fd_cond                                 0
% 2.50/0.97  fd_pseudo_cond                          0
% 2.50/0.97  AC symbols                              0
% 2.50/0.97  
% 2.50/0.97  ------ Schedule dynamic 5 is on 
% 2.50/0.97  
% 2.50/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.50/0.97  
% 2.50/0.97  
% 2.50/0.97  ------ 
% 2.50/0.97  Current options:
% 2.50/0.97  ------ 
% 2.50/0.97  
% 2.50/0.97  ------ Input Options
% 2.50/0.97  
% 2.50/0.97  --out_options                           all
% 2.50/0.97  --tptp_safe_out                         true
% 2.50/0.97  --problem_path                          ""
% 2.50/0.97  --include_path                          ""
% 2.50/0.97  --clausifier                            res/vclausify_rel
% 2.50/0.97  --clausifier_options                    --mode clausify
% 2.50/0.97  --stdin                                 false
% 2.50/0.97  --stats_out                             all
% 2.50/0.97  
% 2.50/0.97  ------ General Options
% 2.50/0.97  
% 2.50/0.97  --fof                                   false
% 2.50/0.97  --time_out_real                         305.
% 2.50/0.97  --time_out_virtual                      -1.
% 2.50/0.97  --symbol_type_check                     false
% 2.50/0.97  --clausify_out                          false
% 2.50/0.97  --sig_cnt_out                           false
% 2.50/0.97  --trig_cnt_out                          false
% 2.50/0.97  --trig_cnt_out_tolerance                1.
% 2.50/0.97  --trig_cnt_out_sk_spl                   false
% 2.50/0.97  --abstr_cl_out                          false
% 2.50/0.97  
% 2.50/0.97  ------ Global Options
% 2.50/0.97  
% 2.50/0.97  --schedule                              default
% 2.50/0.97  --add_important_lit                     false
% 2.50/0.97  --prop_solver_per_cl                    1000
% 2.50/0.97  --min_unsat_core                        false
% 2.50/0.97  --soft_assumptions                      false
% 2.50/0.97  --soft_lemma_size                       3
% 2.50/0.97  --prop_impl_unit_size                   0
% 2.50/0.97  --prop_impl_unit                        []
% 2.50/0.97  --share_sel_clauses                     true
% 2.50/0.97  --reset_solvers                         false
% 2.50/0.97  --bc_imp_inh                            [conj_cone]
% 2.50/0.97  --conj_cone_tolerance                   3.
% 2.50/0.97  --extra_neg_conj                        none
% 2.50/0.97  --large_theory_mode                     true
% 2.50/0.97  --prolific_symb_bound                   200
% 2.50/0.97  --lt_threshold                          2000
% 2.50/0.97  --clause_weak_htbl                      true
% 2.50/0.97  --gc_record_bc_elim                     false
% 2.50/0.97  
% 2.50/0.97  ------ Preprocessing Options
% 2.50/0.97  
% 2.50/0.97  --preprocessing_flag                    true
% 2.50/0.97  --time_out_prep_mult                    0.1
% 2.50/0.97  --splitting_mode                        input
% 2.50/0.97  --splitting_grd                         true
% 2.50/0.97  --splitting_cvd                         false
% 2.50/0.97  --splitting_cvd_svl                     false
% 2.50/0.97  --splitting_nvd                         32
% 2.50/0.97  --sub_typing                            true
% 2.50/0.97  --prep_gs_sim                           true
% 2.50/0.97  --prep_unflatten                        true
% 2.50/0.97  --prep_res_sim                          true
% 2.50/0.97  --prep_upred                            true
% 2.50/0.97  --prep_sem_filter                       exhaustive
% 2.50/0.97  --prep_sem_filter_out                   false
% 2.50/0.97  --pred_elim                             true
% 2.50/0.97  --res_sim_input                         true
% 2.50/0.97  --eq_ax_congr_red                       true
% 2.50/0.97  --pure_diseq_elim                       true
% 2.50/0.97  --brand_transform                       false
% 2.50/0.97  --non_eq_to_eq                          false
% 2.50/0.97  --prep_def_merge                        true
% 2.50/0.97  --prep_def_merge_prop_impl              false
% 2.50/0.97  --prep_def_merge_mbd                    true
% 2.50/0.97  --prep_def_merge_tr_red                 false
% 2.50/0.97  --prep_def_merge_tr_cl                  false
% 2.50/0.97  --smt_preprocessing                     true
% 2.50/0.97  --smt_ac_axioms                         fast
% 2.50/0.97  --preprocessed_out                      false
% 2.50/0.97  --preprocessed_stats                    false
% 2.50/0.97  
% 2.50/0.97  ------ Abstraction refinement Options
% 2.50/0.97  
% 2.50/0.97  --abstr_ref                             []
% 2.50/0.97  --abstr_ref_prep                        false
% 2.50/0.97  --abstr_ref_until_sat                   false
% 2.50/0.97  --abstr_ref_sig_restrict                funpre
% 2.50/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/0.97  --abstr_ref_under                       []
% 2.50/0.97  
% 2.50/0.97  ------ SAT Options
% 2.50/0.97  
% 2.50/0.97  --sat_mode                              false
% 2.50/0.97  --sat_fm_restart_options                ""
% 2.50/0.97  --sat_gr_def                            false
% 2.50/0.97  --sat_epr_types                         true
% 2.50/0.97  --sat_non_cyclic_types                  false
% 2.50/0.97  --sat_finite_models                     false
% 2.50/0.97  --sat_fm_lemmas                         false
% 2.50/0.97  --sat_fm_prep                           false
% 2.50/0.97  --sat_fm_uc_incr                        true
% 2.50/0.97  --sat_out_model                         small
% 2.50/0.97  --sat_out_clauses                       false
% 2.50/0.97  
% 2.50/0.97  ------ QBF Options
% 2.50/0.97  
% 2.50/0.97  --qbf_mode                              false
% 2.50/0.97  --qbf_elim_univ                         false
% 2.50/0.97  --qbf_dom_inst                          none
% 2.50/0.97  --qbf_dom_pre_inst                      false
% 2.50/0.97  --qbf_sk_in                             false
% 2.50/0.97  --qbf_pred_elim                         true
% 2.50/0.97  --qbf_split                             512
% 2.50/0.97  
% 2.50/0.97  ------ BMC1 Options
% 2.50/0.97  
% 2.50/0.97  --bmc1_incremental                      false
% 2.50/0.97  --bmc1_axioms                           reachable_all
% 2.50/0.97  --bmc1_min_bound                        0
% 2.50/0.97  --bmc1_max_bound                        -1
% 2.50/0.97  --bmc1_max_bound_default                -1
% 2.50/0.97  --bmc1_symbol_reachability              true
% 2.50/0.97  --bmc1_property_lemmas                  false
% 2.50/0.97  --bmc1_k_induction                      false
% 2.50/0.97  --bmc1_non_equiv_states                 false
% 2.50/0.97  --bmc1_deadlock                         false
% 2.50/0.97  --bmc1_ucm                              false
% 2.50/0.97  --bmc1_add_unsat_core                   none
% 2.50/0.97  --bmc1_unsat_core_children              false
% 2.50/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/0.97  --bmc1_out_stat                         full
% 2.50/0.97  --bmc1_ground_init                      false
% 2.50/0.97  --bmc1_pre_inst_next_state              false
% 2.50/0.97  --bmc1_pre_inst_state                   false
% 2.50/0.97  --bmc1_pre_inst_reach_state             false
% 2.50/0.97  --bmc1_out_unsat_core                   false
% 2.50/0.97  --bmc1_aig_witness_out                  false
% 2.50/0.97  --bmc1_verbose                          false
% 2.50/0.97  --bmc1_dump_clauses_tptp                false
% 2.50/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.50/0.97  --bmc1_dump_file                        -
% 2.50/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.50/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.50/0.97  --bmc1_ucm_extend_mode                  1
% 2.50/0.97  --bmc1_ucm_init_mode                    2
% 2.50/0.97  --bmc1_ucm_cone_mode                    none
% 2.50/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.50/0.97  --bmc1_ucm_relax_model                  4
% 2.50/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.50/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/0.97  --bmc1_ucm_layered_model                none
% 2.50/0.97  --bmc1_ucm_max_lemma_size               10
% 2.50/0.97  
% 2.50/0.97  ------ AIG Options
% 2.50/0.97  
% 2.50/0.97  --aig_mode                              false
% 2.50/0.97  
% 2.50/0.97  ------ Instantiation Options
% 2.50/0.97  
% 2.50/0.97  --instantiation_flag                    true
% 2.50/0.97  --inst_sos_flag                         false
% 2.50/0.97  --inst_sos_phase                        true
% 2.50/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/0.97  --inst_lit_sel_side                     none
% 2.50/0.97  --inst_solver_per_active                1400
% 2.50/0.97  --inst_solver_calls_frac                1.
% 2.50/0.97  --inst_passive_queue_type               priority_queues
% 2.50/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/0.97  --inst_passive_queues_freq              [25;2]
% 2.50/0.97  --inst_dismatching                      true
% 2.50/0.97  --inst_eager_unprocessed_to_passive     true
% 2.50/0.97  --inst_prop_sim_given                   true
% 2.50/0.97  --inst_prop_sim_new                     false
% 2.50/0.97  --inst_subs_new                         false
% 2.50/0.97  --inst_eq_res_simp                      false
% 2.50/0.97  --inst_subs_given                       false
% 2.50/0.97  --inst_orphan_elimination               true
% 2.50/0.97  --inst_learning_loop_flag               true
% 2.50/0.97  --inst_learning_start                   3000
% 2.50/0.97  --inst_learning_factor                  2
% 2.50/0.97  --inst_start_prop_sim_after_learn       3
% 2.50/0.97  --inst_sel_renew                        solver
% 2.50/0.97  --inst_lit_activity_flag                true
% 2.50/0.97  --inst_restr_to_given                   false
% 2.50/0.97  --inst_activity_threshold               500
% 2.50/0.97  --inst_out_proof                        true
% 2.50/0.97  
% 2.50/0.97  ------ Resolution Options
% 2.50/0.97  
% 2.50/0.97  --resolution_flag                       false
% 2.50/0.97  --res_lit_sel                           adaptive
% 2.50/0.97  --res_lit_sel_side                      none
% 2.50/0.97  --res_ordering                          kbo
% 2.50/0.97  --res_to_prop_solver                    active
% 2.50/0.97  --res_prop_simpl_new                    false
% 2.50/0.97  --res_prop_simpl_given                  true
% 2.50/0.97  --res_passive_queue_type                priority_queues
% 2.50/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/0.97  --res_passive_queues_freq               [15;5]
% 2.50/0.97  --res_forward_subs                      full
% 2.50/0.97  --res_backward_subs                     full
% 2.50/0.97  --res_forward_subs_resolution           true
% 2.50/0.97  --res_backward_subs_resolution          true
% 2.50/0.97  --res_orphan_elimination                true
% 2.50/0.97  --res_time_limit                        2.
% 2.50/0.97  --res_out_proof                         true
% 2.50/0.97  
% 2.50/0.97  ------ Superposition Options
% 2.50/0.97  
% 2.50/0.97  --superposition_flag                    true
% 2.50/0.97  --sup_passive_queue_type                priority_queues
% 2.50/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.50/0.97  --demod_completeness_check              fast
% 2.50/0.97  --demod_use_ground                      true
% 2.50/0.97  --sup_to_prop_solver                    passive
% 2.50/0.97  --sup_prop_simpl_new                    true
% 2.50/0.97  --sup_prop_simpl_given                  true
% 2.50/0.97  --sup_fun_splitting                     false
% 2.50/0.97  --sup_smt_interval                      50000
% 2.50/0.97  
% 2.50/0.97  ------ Superposition Simplification Setup
% 2.50/0.97  
% 2.50/0.97  --sup_indices_passive                   []
% 2.50/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.97  --sup_full_bw                           [BwDemod]
% 2.50/0.97  --sup_immed_triv                        [TrivRules]
% 2.50/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.97  --sup_immed_bw_main                     []
% 2.50/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.97  
% 2.50/0.97  ------ Combination Options
% 2.50/0.97  
% 2.50/0.97  --comb_res_mult                         3
% 2.50/0.97  --comb_sup_mult                         2
% 2.50/0.97  --comb_inst_mult                        10
% 2.50/0.97  
% 2.50/0.97  ------ Debug Options
% 2.50/0.97  
% 2.50/0.97  --dbg_backtrace                         false
% 2.50/0.97  --dbg_dump_prop_clauses                 false
% 2.50/0.97  --dbg_dump_prop_clauses_file            -
% 2.50/0.97  --dbg_out_stat                          false
% 2.50/0.97  
% 2.50/0.97  
% 2.50/0.97  
% 2.50/0.97  
% 2.50/0.97  ------ Proving...
% 2.50/0.97  
% 2.50/0.97  
% 2.50/0.97  % SZS status Theorem for theBenchmark.p
% 2.50/0.97  
% 2.50/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.50/0.97  
% 2.50/0.97  fof(f10,axiom,(
% 2.50/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.50/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.97  
% 2.50/0.97  fof(f33,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.50/0.97    inference(ennf_transformation,[],[f10])).
% 2.50/0.97  
% 2.50/0.97  fof(f34,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.50/0.97    inference(flattening,[],[f33])).
% 2.50/0.97  
% 2.50/0.97  fof(f46,plain,(
% 2.50/0.97    ! [X2,X1,X0] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => (r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_connsp_2(sK1(X0,X1,X2),X0,X1) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK1(X0,X1,X2))))),
% 2.50/0.97    introduced(choice_axiom,[])).
% 2.50/0.97  
% 2.50/0.97  fof(f47,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_connsp_2(sK1(X0,X1,X2),X0,X1) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK1(X0,X1,X2))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.50/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f46])).
% 2.50/0.97  
% 2.50/0.97  fof(f71,plain,(
% 2.50/0.97    ( ! [X2,X0,X1] : (m1_connsp_2(sK1(X0,X1,X2),X0,X1) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f47])).
% 2.50/0.97  
% 2.50/0.97  fof(f6,axiom,(
% 2.50/0.97    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.50/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.97  
% 2.50/0.97  fof(f25,plain,(
% 2.50/0.97    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.50/0.97    inference(ennf_transformation,[],[f6])).
% 2.50/0.97  
% 2.50/0.97  fof(f26,plain,(
% 2.50/0.97    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.50/0.97    inference(flattening,[],[f25])).
% 2.50/0.97  
% 2.50/0.97  fof(f65,plain,(
% 2.50/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f26])).
% 2.50/0.97  
% 2.50/0.97  fof(f15,conjecture,(
% 2.50/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.50/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.97  
% 2.50/0.97  fof(f16,negated_conjecture,(
% 2.50/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.50/0.97    inference(negated_conjecture,[],[f15])).
% 2.50/0.97  
% 2.50/0.97  fof(f42,plain,(
% 2.50/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.50/0.97    inference(ennf_transformation,[],[f16])).
% 2.50/0.97  
% 2.50/0.97  fof(f43,plain,(
% 2.50/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.50/0.97    inference(flattening,[],[f42])).
% 2.50/0.97  
% 2.50/0.97  fof(f51,plain,(
% 2.50/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.50/0.97    inference(nnf_transformation,[],[f43])).
% 2.50/0.97  
% 2.50/0.97  fof(f52,plain,(
% 2.50/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.50/0.97    inference(flattening,[],[f51])).
% 2.50/0.97  
% 2.50/0.97  fof(f58,plain,(
% 2.50/0.97    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7) | r1_tmap_1(X1,X0,X2,X4)) & sK7 = X4 & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 2.50/0.97    introduced(choice_axiom,[])).
% 2.50/0.97  
% 2.50/0.97  fof(f57,plain,(
% 2.50/0.97    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK6)) & sK6 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK6,u1_struct_0(X1)))) )),
% 2.50/0.97    introduced(choice_axiom,[])).
% 2.50/0.97  
% 2.50/0.97  fof(f56,plain,(
% 2.50/0.97    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK5))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK5,X1) & v1_tsep_1(sK5,X1) & ~v2_struct_0(sK5))) )),
% 2.50/0.97    introduced(choice_axiom,[])).
% 2.50/0.97  
% 2.50/0.97  fof(f55,plain,(
% 2.50/0.97    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5) | ~r1_tmap_1(X1,X0,sK4,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5) | r1_tmap_1(X1,X0,sK4,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 2.50/0.97    introduced(choice_axiom,[])).
% 2.50/0.97  
% 2.50/0.97  fof(f54,plain,(
% 2.50/0.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5) | ~r1_tmap_1(sK3,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5) | r1_tmap_1(sK3,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK3))) & m1_pre_topc(X3,sK3) & v1_tsep_1(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 2.50/0.97    introduced(choice_axiom,[])).
% 2.50/0.97  
% 2.50/0.97  fof(f53,plain,(
% 2.50/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5) | ~r1_tmap_1(X1,sK2,X2,X4)) & (r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5) | r1_tmap_1(X1,sK2,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.50/0.97    introduced(choice_axiom,[])).
% 2.50/0.97  
% 2.50/0.97  fof(f59,plain,(
% 2.50/0.97    ((((((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~r1_tmap_1(sK3,sK2,sK4,sK6)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | r1_tmap_1(sK3,sK2,sK4,sK6)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK5))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_pre_topc(sK5,sK3) & v1_tsep_1(sK5,sK3) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.50/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f52,f58,f57,f56,f55,f54,f53])).
% 2.50/0.97  
% 2.50/0.97  fof(f85,plain,(
% 2.50/0.97    v2_pre_topc(sK3)),
% 2.50/0.97    inference(cnf_transformation,[],[f59])).
% 2.50/0.97  
% 2.50/0.97  fof(f84,plain,(
% 2.50/0.97    ~v2_struct_0(sK3)),
% 2.50/0.97    inference(cnf_transformation,[],[f59])).
% 2.50/0.97  
% 2.50/0.97  fof(f86,plain,(
% 2.50/0.97    l1_pre_topc(sK3)),
% 2.50/0.97    inference(cnf_transformation,[],[f59])).
% 2.50/0.97  
% 2.50/0.97  fof(f9,axiom,(
% 2.50/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 2.50/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.97  
% 2.50/0.97  fof(f31,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.50/0.97    inference(ennf_transformation,[],[f9])).
% 2.50/0.97  
% 2.50/0.97  fof(f32,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.50/0.97    inference(flattening,[],[f31])).
% 2.50/0.97  
% 2.50/0.97  fof(f68,plain,(
% 2.50/0.97    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f32])).
% 2.50/0.97  
% 2.50/0.97  fof(f73,plain,(
% 2.50/0.97    ( ! [X2,X0,X1] : (r1_tarski(sK1(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f47])).
% 2.50/0.97  
% 2.50/0.97  fof(f70,plain,(
% 2.50/0.97    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f47])).
% 2.50/0.97  
% 2.50/0.97  fof(f96,plain,(
% 2.50/0.97    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | r1_tmap_1(sK3,sK2,sK4,sK6)),
% 2.50/0.97    inference(cnf_transformation,[],[f59])).
% 2.50/0.97  
% 2.50/0.97  fof(f95,plain,(
% 2.50/0.97    sK6 = sK7),
% 2.50/0.97    inference(cnf_transformation,[],[f59])).
% 2.50/0.97  
% 2.50/0.97  fof(f92,plain,(
% 2.50/0.97    m1_pre_topc(sK5,sK3)),
% 2.50/0.97    inference(cnf_transformation,[],[f59])).
% 2.50/0.97  
% 2.50/0.97  fof(f14,axiom,(
% 2.50/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.50/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.97  
% 2.50/0.97  fof(f40,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.50/0.97    inference(ennf_transformation,[],[f14])).
% 2.50/0.97  
% 2.50/0.97  fof(f41,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.50/0.97    inference(flattening,[],[f40])).
% 2.50/0.97  
% 2.50/0.97  fof(f50,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.50/0.97    inference(nnf_transformation,[],[f41])).
% 2.50/0.97  
% 2.50/0.97  fof(f80,plain,(
% 2.50/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f50])).
% 2.50/0.97  
% 2.50/0.97  fof(f102,plain,(
% 2.50/0.97    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/0.97    inference(equality_resolution,[],[f80])).
% 2.50/0.97  
% 2.50/0.97  fof(f88,plain,(
% 2.50/0.97    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 2.50/0.97    inference(cnf_transformation,[],[f59])).
% 2.50/0.97  
% 2.50/0.97  fof(f87,plain,(
% 2.50/0.97    v1_funct_1(sK4)),
% 2.50/0.97    inference(cnf_transformation,[],[f59])).
% 2.50/0.97  
% 2.50/0.97  fof(f5,axiom,(
% 2.50/0.97    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.50/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.97  
% 2.50/0.97  fof(f23,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.50/0.97    inference(ennf_transformation,[],[f5])).
% 2.50/0.97  
% 2.50/0.97  fof(f24,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.50/0.97    inference(flattening,[],[f23])).
% 2.50/0.97  
% 2.50/0.97  fof(f64,plain,(
% 2.50/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f24])).
% 2.50/0.97  
% 2.50/0.97  fof(f90,plain,(
% 2.50/0.97    ~v2_struct_0(sK5)),
% 2.50/0.97    inference(cnf_transformation,[],[f59])).
% 2.50/0.97  
% 2.50/0.97  fof(f82,plain,(
% 2.50/0.97    v2_pre_topc(sK2)),
% 2.50/0.97    inference(cnf_transformation,[],[f59])).
% 2.50/0.97  
% 2.50/0.97  fof(f81,plain,(
% 2.50/0.97    ~v2_struct_0(sK2)),
% 2.50/0.97    inference(cnf_transformation,[],[f59])).
% 2.50/0.97  
% 2.50/0.97  fof(f83,plain,(
% 2.50/0.97    l1_pre_topc(sK2)),
% 2.50/0.97    inference(cnf_transformation,[],[f59])).
% 2.50/0.97  
% 2.50/0.97  fof(f89,plain,(
% 2.50/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 2.50/0.97    inference(cnf_transformation,[],[f59])).
% 2.50/0.97  
% 2.50/0.97  fof(f94,plain,(
% 2.50/0.97    m1_subset_1(sK7,u1_struct_0(sK5))),
% 2.50/0.97    inference(cnf_transformation,[],[f59])).
% 2.50/0.97  
% 2.50/0.97  fof(f79,plain,(
% 2.50/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f50])).
% 2.50/0.97  
% 2.50/0.97  fof(f103,plain,(
% 2.50/0.97    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/0.97    inference(equality_resolution,[],[f79])).
% 2.50/0.97  
% 2.50/0.97  fof(f13,axiom,(
% 2.50/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.50/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.97  
% 2.50/0.97  fof(f38,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.50/0.97    inference(ennf_transformation,[],[f13])).
% 2.50/0.97  
% 2.50/0.97  fof(f39,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.50/0.97    inference(flattening,[],[f38])).
% 2.50/0.97  
% 2.50/0.97  fof(f78,plain,(
% 2.50/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f39])).
% 2.50/0.97  
% 2.50/0.97  fof(f101,plain,(
% 2.50/0.97    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/0.97    inference(equality_resolution,[],[f78])).
% 2.50/0.97  
% 2.50/0.97  fof(f97,plain,(
% 2.50/0.97    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~r1_tmap_1(sK3,sK2,sK4,sK6)),
% 2.50/0.97    inference(cnf_transformation,[],[f59])).
% 2.50/0.97  
% 2.50/0.97  fof(f72,plain,(
% 2.50/0.97    ( ! [X2,X0,X1] : (v3_pre_topc(sK1(X0,X1,X2),X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f47])).
% 2.50/0.97  
% 2.50/0.97  fof(f2,axiom,(
% 2.50/0.97    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.50/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.97  
% 2.50/0.97  fof(f19,plain,(
% 2.50/0.97    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.50/0.97    inference(ennf_transformation,[],[f2])).
% 2.50/0.97  
% 2.50/0.97  fof(f61,plain,(
% 2.50/0.97    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f19])).
% 2.50/0.97  
% 2.50/0.97  fof(f8,axiom,(
% 2.50/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 2.50/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.97  
% 2.50/0.97  fof(f29,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.50/0.97    inference(ennf_transformation,[],[f8])).
% 2.50/0.97  
% 2.50/0.97  fof(f30,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.50/0.97    inference(flattening,[],[f29])).
% 2.50/0.97  
% 2.50/0.97  fof(f67,plain,(
% 2.50/0.97    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f30])).
% 2.50/0.97  
% 2.50/0.97  fof(f3,axiom,(
% 2.50/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.50/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.97  
% 2.50/0.97  fof(f20,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.50/0.97    inference(ennf_transformation,[],[f3])).
% 2.50/0.97  
% 2.50/0.97  fof(f21,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.50/0.97    inference(flattening,[],[f20])).
% 2.50/0.97  
% 2.50/0.97  fof(f62,plain,(
% 2.50/0.97    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f21])).
% 2.50/0.97  
% 2.50/0.97  fof(f4,axiom,(
% 2.50/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.50/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.97  
% 2.50/0.97  fof(f22,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.50/0.97    inference(ennf_transformation,[],[f4])).
% 2.50/0.97  
% 2.50/0.97  fof(f63,plain,(
% 2.50/0.97    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f22])).
% 2.50/0.97  
% 2.50/0.97  fof(f1,axiom,(
% 2.50/0.97    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.50/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.97  
% 2.50/0.97  fof(f17,plain,(
% 2.50/0.97    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.50/0.97    inference(ennf_transformation,[],[f1])).
% 2.50/0.97  
% 2.50/0.97  fof(f18,plain,(
% 2.50/0.97    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.50/0.97    inference(flattening,[],[f17])).
% 2.50/0.97  
% 2.50/0.97  fof(f60,plain,(
% 2.50/0.97    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f18])).
% 2.50/0.97  
% 2.50/0.97  fof(f7,axiom,(
% 2.50/0.97    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 2.50/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.97  
% 2.50/0.97  fof(f27,plain,(
% 2.50/0.97    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.50/0.97    inference(ennf_transformation,[],[f7])).
% 2.50/0.97  
% 2.50/0.97  fof(f28,plain,(
% 2.50/0.97    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.50/0.97    inference(flattening,[],[f27])).
% 2.50/0.97  
% 2.50/0.97  fof(f44,plain,(
% 2.50/0.97    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK0(X0,X1),X0,X1))),
% 2.50/0.97    introduced(choice_axiom,[])).
% 2.50/0.97  
% 2.50/0.97  fof(f45,plain,(
% 2.50/0.97    ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.50/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f44])).
% 2.50/0.97  
% 2.50/0.97  fof(f66,plain,(
% 2.50/0.97    ( ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f45])).
% 2.50/0.97  
% 2.50/0.97  fof(f93,plain,(
% 2.50/0.97    m1_subset_1(sK6,u1_struct_0(sK3))),
% 2.50/0.97    inference(cnf_transformation,[],[f59])).
% 2.50/0.97  
% 2.50/0.97  fof(f12,axiom,(
% 2.50/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.50/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.97  
% 2.50/0.97  fof(f37,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.50/0.97    inference(ennf_transformation,[],[f12])).
% 2.50/0.97  
% 2.50/0.97  fof(f77,plain,(
% 2.50/0.97    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f37])).
% 2.50/0.97  
% 2.50/0.97  fof(f11,axiom,(
% 2.50/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.50/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.97  
% 2.50/0.97  fof(f35,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.50/0.97    inference(ennf_transformation,[],[f11])).
% 2.50/0.97  
% 2.50/0.97  fof(f36,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.50/0.97    inference(flattening,[],[f35])).
% 2.50/0.97  
% 2.50/0.97  fof(f48,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.50/0.97    inference(nnf_transformation,[],[f36])).
% 2.50/0.97  
% 2.50/0.97  fof(f49,plain,(
% 2.50/0.97    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.50/0.97    inference(flattening,[],[f48])).
% 2.50/0.97  
% 2.50/0.97  fof(f74,plain,(
% 2.50/0.97    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.50/0.97    inference(cnf_transformation,[],[f49])).
% 2.50/0.97  
% 2.50/0.97  fof(f100,plain,(
% 2.50/0.97    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.50/0.97    inference(equality_resolution,[],[f74])).
% 2.50/0.97  
% 2.50/0.97  fof(f91,plain,(
% 2.50/0.97    v1_tsep_1(sK5,sK3)),
% 2.50/0.97    inference(cnf_transformation,[],[f59])).
% 2.50/0.97  
% 2.50/0.97  cnf(c_11,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(cnf_transformation,[],[f71]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_5,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(cnf_transformation,[],[f65]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_236,plain,
% 2.50/0.97      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
% 2.50/0.97      | ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_11,c_5]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_237,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(renaming,[status(thm)],[c_236]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_33,negated_conjecture,
% 2.50/0.97      ( v2_pre_topc(sK3) ),
% 2.50/0.97      inference(cnf_transformation,[],[f85]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1784,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | sK3 != X1 ),
% 2.50/0.97      inference(resolution_lifted,[status(thm)],[c_237,c_33]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1785,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.50/0.97      | m1_connsp_2(sK1(sK3,X1,X0),sK3,X1)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.50/0.97      | v2_struct_0(sK3)
% 2.50/0.97      | ~ l1_pre_topc(sK3) ),
% 2.50/0.97      inference(unflattening,[status(thm)],[c_1784]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_34,negated_conjecture,
% 2.50/0.97      ( ~ v2_struct_0(sK3) ),
% 2.50/0.97      inference(cnf_transformation,[],[f84]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_32,negated_conjecture,
% 2.50/0.97      ( l1_pre_topc(sK3) ),
% 2.50/0.97      inference(cnf_transformation,[],[f86]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1789,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.50/0.97      | m1_connsp_2(sK1(sK3,X1,X0),sK3,X1)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_1785,c_34,c_32]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4611,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0_54,sK3,X1_54)
% 2.50/0.97      | m1_connsp_2(sK1(sK3,X1_54,X0_54),sK3,X1_54)
% 2.50/0.97      | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_1789]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_5745,plain,
% 2.50/0.97      ( m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
% 2.50/0.97      | m1_connsp_2(sK1(sK3,X1_54,X0_54),sK3,X1_54) = iProver_top
% 2.50/0.97      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_4611]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_8,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.97      | r2_hidden(X2,X0)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(cnf_transformation,[],[f68]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_257,plain,
% 2.50/0.97      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | r2_hidden(X2,X0)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(global_propositional_subsumption,[status(thm)],[c_8,c_5]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_258,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | r2_hidden(X2,X0)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(renaming,[status(thm)],[c_257]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1721,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | r2_hidden(X2,X0)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | sK3 != X1 ),
% 2.50/0.97      inference(resolution_lifted,[status(thm)],[c_258,c_33]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1722,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.50/0.97      | r2_hidden(X1,X0)
% 2.50/0.97      | v2_struct_0(sK3)
% 2.50/0.97      | ~ l1_pre_topc(sK3) ),
% 2.50/0.97      inference(unflattening,[status(thm)],[c_1721]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1726,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.50/0.97      | r2_hidden(X1,X0) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_1722,c_34,c_32]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4614,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0_54,sK3,X1_54)
% 2.50/0.97      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 2.50/0.97      | r2_hidden(X1_54,X0_54) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_1726]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_5742,plain,
% 2.50/0.97      ( m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
% 2.50/0.97      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.50/0.97      | r2_hidden(X1_54,X0_54) = iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_4614]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_7425,plain,
% 2.50/0.97      ( m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
% 2.50/0.97      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.50/0.97      | r2_hidden(X1_54,sK1(sK3,X1_54,X0_54)) = iProver_top ),
% 2.50/0.97      inference(superposition,[status(thm)],[c_5745,c_5742]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_9,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | r1_tarski(sK1(X1,X2,X0),X0)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(cnf_transformation,[],[f73]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_250,plain,
% 2.50/0.97      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | r1_tarski(sK1(X1,X2,X0),X0)
% 2.50/0.97      | ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(global_propositional_subsumption,[status(thm)],[c_9,c_5]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_251,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | r1_tarski(sK1(X1,X2,X0),X0)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(renaming,[status(thm)],[c_250]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1742,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | r1_tarski(sK1(X1,X2,X0),X0)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | sK3 != X1 ),
% 2.50/0.97      inference(resolution_lifted,[status(thm)],[c_251,c_33]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1743,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.50/0.97      | r1_tarski(sK1(sK3,X1,X0),X0)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.50/0.97      | v2_struct_0(sK3)
% 2.50/0.97      | ~ l1_pre_topc(sK3) ),
% 2.50/0.97      inference(unflattening,[status(thm)],[c_1742]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1747,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.50/0.97      | r1_tarski(sK1(sK3,X1,X0),X0)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_1743,c_34,c_32]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4613,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0_54,sK3,X1_54)
% 2.50/0.97      | r1_tarski(sK1(sK3,X1_54,X0_54),X0_54)
% 2.50/0.97      | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_1747]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_5743,plain,
% 2.50/0.97      ( m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
% 2.50/0.97      | r1_tarski(sK1(sK3,X1_54,X0_54),X0_54) = iProver_top
% 2.50/0.97      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_4613]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_12,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.97      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(cnf_transformation,[],[f70]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_229,plain,
% 2.50/0.97      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_12,c_5]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_230,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(renaming,[status(thm)],[c_229]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1805,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | sK3 != X1 ),
% 2.50/0.97      inference(resolution_lifted,[status(thm)],[c_230,c_33]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1806,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.50/0.97      | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.50/0.97      | v2_struct_0(sK3)
% 2.50/0.97      | ~ l1_pre_topc(sK3) ),
% 2.50/0.97      inference(unflattening,[status(thm)],[c_1805]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1810,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.50/0.97      | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_1806,c_34,c_32]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4610,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0_54,sK3,X1_54)
% 2.50/0.97      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 2.50/0.97      | m1_subset_1(sK1(sK3,X1_54,X0_54),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_1810]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_5746,plain,
% 2.50/0.97      ( m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
% 2.50/0.97      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.50/0.97      | m1_subset_1(sK1(sK3,X1_54,X0_54),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_4610]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_22,negated_conjecture,
% 2.50/0.97      ( r1_tmap_1(sK3,sK2,sK4,sK6)
% 2.50/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 2.50/0.97      inference(cnf_transformation,[],[f96]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4631,negated_conjecture,
% 2.50/0.97      ( r1_tmap_1(sK3,sK2,sK4,sK6)
% 2.50/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_22]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_5722,plain,
% 2.50/0.97      ( r1_tmap_1(sK3,sK2,sK4,sK6) = iProver_top
% 2.50/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_4631]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_23,negated_conjecture,
% 2.50/0.97      ( sK6 = sK7 ),
% 2.50/0.97      inference(cnf_transformation,[],[f95]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4630,negated_conjecture,
% 2.50/0.97      ( sK6 = sK7 ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_23]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_5801,plain,
% 2.50/0.97      ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
% 2.50/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
% 2.50/0.97      inference(light_normalisation,[status(thm)],[c_5722,c_4630]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_26,negated_conjecture,
% 2.50/0.97      ( m1_pre_topc(sK5,sK3) ),
% 2.50/0.97      inference(cnf_transformation,[],[f92]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_19,plain,
% 2.50/0.97      ( r1_tmap_1(X0,X1,X2,X3)
% 2.50/0.97      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.50/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.50/0.97      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.50/0.97      | ~ v3_pre_topc(X5,X0)
% 2.50/0.97      | ~ m1_pre_topc(X4,X0)
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.50/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.50/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.50/0.97      | ~ r2_hidden(X3,X5)
% 2.50/0.97      | ~ v1_funct_1(X2)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | v2_struct_0(X4)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ l1_pre_topc(X0)
% 2.50/0.97      | ~ v2_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X0) ),
% 2.50/0.97      inference(cnf_transformation,[],[f102]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_30,negated_conjecture,
% 2.50/0.97      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 2.50/0.97      inference(cnf_transformation,[],[f88]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_690,plain,
% 2.50/0.97      ( r1_tmap_1(X0,X1,X2,X3)
% 2.50/0.97      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.50/0.97      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.50/0.97      | ~ v3_pre_topc(X5,X0)
% 2.50/0.97      | ~ m1_pre_topc(X4,X0)
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.50/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.50/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.50/0.97      | ~ r2_hidden(X3,X5)
% 2.50/0.97      | ~ v1_funct_1(X2)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | v2_struct_0(X4)
% 2.50/0.97      | ~ l1_pre_topc(X0)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X0)
% 2.50/0.97      | ~ v2_pre_topc(X1)
% 2.50/0.97      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.50/0.97      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.50/0.97      | sK4 != X2 ),
% 2.50/0.97      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_691,plain,
% 2.50/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.50/0.97      | r1_tmap_1(X2,X1,sK4,X3)
% 2.50/0.97      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.50/0.97      | ~ v3_pre_topc(X4,X2)
% 2.50/0.97      | ~ m1_pre_topc(X0,X2)
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.50/0.97      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.50/0.97      | ~ r2_hidden(X3,X4)
% 2.50/0.97      | ~ v1_funct_1(sK4)
% 2.50/0.97      | v2_struct_0(X2)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | ~ l1_pre_topc(X2)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X2)
% 2.50/0.97      | ~ v2_pre_topc(X1)
% 2.50/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.50/0.97      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.50/0.97      inference(unflattening,[status(thm)],[c_690]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_31,negated_conjecture,
% 2.50/0.97      ( v1_funct_1(sK4) ),
% 2.50/0.97      inference(cnf_transformation,[],[f87]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_695,plain,
% 2.50/0.97      ( ~ r2_hidden(X3,X4)
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.50/0.97      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.50/0.97      | ~ m1_pre_topc(X0,X2)
% 2.50/0.97      | ~ v3_pre_topc(X4,X2)
% 2.50/0.97      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.50/0.97      | r1_tmap_1(X2,X1,sK4,X3)
% 2.50/0.97      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.50/0.97      | v2_struct_0(X2)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | ~ l1_pre_topc(X2)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X2)
% 2.50/0.97      | ~ v2_pre_topc(X1)
% 2.50/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.50/0.97      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_691,c_31]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_696,plain,
% 2.50/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.50/0.97      | r1_tmap_1(X2,X1,sK4,X3)
% 2.50/0.97      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.50/0.97      | ~ v3_pre_topc(X4,X2)
% 2.50/0.97      | ~ m1_pre_topc(X0,X2)
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.50/0.97      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.50/0.97      | ~ r2_hidden(X3,X4)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | v2_struct_0(X2)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ l1_pre_topc(X2)
% 2.50/0.97      | ~ v2_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X2)
% 2.50/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.50/0.97      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.50/0.97      inference(renaming,[status(thm)],[c_695]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4,plain,
% 2.50/0.97      ( ~ m1_pre_topc(X0,X1)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.50/0.97      | m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | ~ l1_pre_topc(X1) ),
% 2.50/0.97      inference(cnf_transformation,[],[f64]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_739,plain,
% 2.50/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.50/0.97      | r1_tmap_1(X2,X1,sK4,X3)
% 2.50/0.97      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.50/0.97      | ~ v3_pre_topc(X4,X2)
% 2.50/0.97      | ~ m1_pre_topc(X0,X2)
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.50/0.97      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.50/0.97      | ~ r2_hidden(X3,X4)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | v2_struct_0(X2)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ l1_pre_topc(X2)
% 2.50/0.97      | ~ v2_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X2)
% 2.50/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.50/0.97      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.50/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_696,c_4]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_911,plain,
% 2.50/0.97      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.50/0.97      | r1_tmap_1(X2,X1,sK4,X3)
% 2.50/0.97      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.50/0.97      | ~ v3_pre_topc(X4,X2)
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.50/0.97      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.50/0.97      | ~ r2_hidden(X3,X4)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | v2_struct_0(X2)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X2)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X2)
% 2.50/0.97      | ~ v2_pre_topc(X1)
% 2.50/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.50/0.97      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.50/0.97      | sK3 != X2
% 2.50/0.97      | sK5 != X0 ),
% 2.50/0.97      inference(resolution_lifted,[status(thm)],[c_26,c_739]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_912,plain,
% 2.50/0.97      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.50/0.97      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.50/0.97      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.50/0.97      | ~ v3_pre_topc(X2,sK3)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.50/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.50/0.97      | ~ r2_hidden(X1,X2)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | v2_struct_0(sK3)
% 2.50/0.97      | v2_struct_0(sK5)
% 2.50/0.97      | ~ l1_pre_topc(X0)
% 2.50/0.97      | ~ l1_pre_topc(sK3)
% 2.50/0.97      | ~ v2_pre_topc(X0)
% 2.50/0.97      | ~ v2_pre_topc(sK3)
% 2.50/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.50/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.50/0.97      inference(unflattening,[status(thm)],[c_911]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_28,negated_conjecture,
% 2.50/0.97      ( ~ v2_struct_0(sK5) ),
% 2.50/0.97      inference(cnf_transformation,[],[f90]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_916,plain,
% 2.50/0.97      ( ~ v2_pre_topc(X0)
% 2.50/0.97      | r1_tmap_1(sK3,X0,sK4,X1)
% 2.50/0.97      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.50/0.97      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.50/0.97      | ~ v3_pre_topc(X2,sK3)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.50/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.50/0.97      | ~ r2_hidden(X1,X2)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | ~ l1_pre_topc(X0)
% 2.50/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.50/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_912,c_34,c_33,c_32,c_28]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_917,plain,
% 2.50/0.97      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.50/0.97      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.50/0.97      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.50/0.97      | ~ v3_pre_topc(X2,sK3)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.50/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.50/0.97      | ~ r2_hidden(X1,X2)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | ~ l1_pre_topc(X0)
% 2.50/0.97      | ~ v2_pre_topc(X0)
% 2.50/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.50/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.50/0.97      inference(renaming,[status(thm)],[c_916]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_36,negated_conjecture,
% 2.50/0.97      ( v2_pre_topc(sK2) ),
% 2.50/0.97      inference(cnf_transformation,[],[f82]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1583,plain,
% 2.50/0.97      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.50/0.97      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.50/0.97      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.50/0.97      | ~ v3_pre_topc(X2,sK3)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.50/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.50/0.97      | ~ r2_hidden(X1,X2)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | ~ l1_pre_topc(X0)
% 2.50/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.50/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.50/0.97      | sK2 != X0 ),
% 2.50/0.97      inference(resolution_lifted,[status(thm)],[c_917,c_36]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1584,plain,
% 2.50/0.97      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.50/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.50/0.97      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.50/0.97      | ~ v3_pre_topc(X1,sK3)
% 2.50/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.50/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 2.50/0.97      | ~ r2_hidden(X0,X1)
% 2.50/0.97      | v2_struct_0(sK2)
% 2.50/0.97      | ~ l1_pre_topc(sK2)
% 2.50/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.50/0.97      inference(unflattening,[status(thm)],[c_1583]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_37,negated_conjecture,
% 2.50/0.97      ( ~ v2_struct_0(sK2) ),
% 2.50/0.97      inference(cnf_transformation,[],[f81]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_35,negated_conjecture,
% 2.50/0.97      ( l1_pre_topc(sK2) ),
% 2.50/0.97      inference(cnf_transformation,[],[f83]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_29,negated_conjecture,
% 2.50/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 2.50/0.97      inference(cnf_transformation,[],[f89]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1588,plain,
% 2.50/0.97      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.50/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.50/0.97      | ~ v3_pre_topc(X1,sK3)
% 2.50/0.97      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.50/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.50/0.97      | r1_tmap_1(sK3,sK2,sK4,X0)
% 2.50/0.97      | ~ r2_hidden(X0,X1)
% 2.50/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_1584,c_37,c_35,c_29]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1589,plain,
% 2.50/0.97      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.50/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.50/0.97      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.50/0.97      | ~ v3_pre_topc(X1,sK3)
% 2.50/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.50/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.50/0.97      | ~ r2_hidden(X0,X1)
% 2.50/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.50/0.97      inference(renaming,[status(thm)],[c_1588]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4619,plain,
% 2.50/0.97      ( r1_tmap_1(sK3,sK2,sK4,X0_54)
% 2.50/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
% 2.50/0.97      | ~ r1_tarski(X1_54,u1_struct_0(sK5))
% 2.50/0.97      | ~ v3_pre_topc(X1_54,sK3)
% 2.50/0.97      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 2.50/0.97      | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.50/0.97      | ~ r2_hidden(X0_54,X1_54)
% 2.50/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_1589]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_5735,plain,
% 2.50/0.97      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.50/0.97      | r1_tmap_1(sK3,sK2,sK4,X0_54) = iProver_top
% 2.50/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54) != iProver_top
% 2.50/0.97      | r1_tarski(X1_54,u1_struct_0(sK5)) != iProver_top
% 2.50/0.97      | v3_pre_topc(X1_54,sK3) != iProver_top
% 2.50/0.97      | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top
% 2.50/0.97      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.50/0.97      | r2_hidden(X0_54,X1_54) != iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_4619]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_6052,plain,
% 2.50/0.97      ( r1_tmap_1(sK3,sK2,sK4,X0_54) = iProver_top
% 2.50/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54) != iProver_top
% 2.50/0.97      | r1_tarski(X1_54,u1_struct_0(sK5)) != iProver_top
% 2.50/0.97      | v3_pre_topc(X1_54,sK3) != iProver_top
% 2.50/0.97      | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top
% 2.50/0.97      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.50/0.97      | r2_hidden(X0_54,X1_54) != iProver_top ),
% 2.50/0.97      inference(equality_resolution_simp,[status(thm)],[c_5735]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_9184,plain,
% 2.50/0.97      ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
% 2.50/0.97      | r1_tarski(X0_54,u1_struct_0(sK5)) != iProver_top
% 2.50/0.97      | v3_pre_topc(X0_54,sK3) != iProver_top
% 2.50/0.97      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.50/0.97      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
% 2.50/0.97      | r2_hidden(sK7,X0_54) != iProver_top ),
% 2.50/0.97      inference(superposition,[status(thm)],[c_5801,c_6052]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_24,negated_conjecture,
% 2.50/0.97      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 2.50/0.97      inference(cnf_transformation,[],[f94]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_51,plain,
% 2.50/0.97      ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_20,plain,
% 2.50/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.50/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.50/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.50/0.97      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.50/0.97      | ~ v3_pre_topc(X5,X0)
% 2.50/0.97      | ~ m1_pre_topc(X4,X0)
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.50/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.50/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.50/0.97      | ~ r2_hidden(X3,X5)
% 2.50/0.97      | ~ v1_funct_1(X2)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | v2_struct_0(X4)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ l1_pre_topc(X0)
% 2.50/0.97      | ~ v2_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X0) ),
% 2.50/0.97      inference(cnf_transformation,[],[f103]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_18,plain,
% 2.50/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.50/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.50/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.50/0.97      | ~ m1_pre_topc(X4,X0)
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.50/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.50/0.97      | ~ v1_funct_1(X2)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | v2_struct_0(X4)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ l1_pre_topc(X0)
% 2.50/0.97      | ~ v2_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X0) ),
% 2.50/0.97      inference(cnf_transformation,[],[f101]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_200,plain,
% 2.50/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.50/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.50/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.50/0.97      | ~ m1_pre_topc(X4,X0)
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.50/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.50/0.97      | ~ v1_funct_1(X2)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | v2_struct_0(X4)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ l1_pre_topc(X0)
% 2.50/0.97      | ~ v2_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X0) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_20,c_18]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_201,plain,
% 2.50/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.50/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.50/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.50/0.97      | ~ m1_pre_topc(X4,X0)
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.50/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.50/0.97      | ~ v1_funct_1(X2)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | v2_struct_0(X4)
% 2.50/0.97      | ~ l1_pre_topc(X0)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X0)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(renaming,[status(thm)],[c_200]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_633,plain,
% 2.50/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.50/0.97      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.50/0.97      | ~ m1_pre_topc(X4,X0)
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.50/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.50/0.97      | ~ v1_funct_1(X2)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | v2_struct_0(X4)
% 2.50/0.97      | ~ l1_pre_topc(X0)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X0)
% 2.50/0.97      | ~ v2_pre_topc(X1)
% 2.50/0.97      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.50/0.97      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.50/0.97      | sK4 != X2 ),
% 2.50/0.97      inference(resolution_lifted,[status(thm)],[c_201,c_30]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_634,plain,
% 2.50/0.97      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.50/0.97      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.50/0.97      | ~ m1_pre_topc(X0,X2)
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.50/0.97      | ~ v1_funct_1(sK4)
% 2.50/0.97      | v2_struct_0(X2)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | ~ l1_pre_topc(X2)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X2)
% 2.50/0.97      | ~ v2_pre_topc(X1)
% 2.50/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.50/0.97      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.50/0.97      inference(unflattening,[status(thm)],[c_633]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_638,plain,
% 2.50/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.50/0.97      | ~ m1_pre_topc(X0,X2)
% 2.50/0.97      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.50/0.97      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.50/0.97      | v2_struct_0(X2)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | ~ l1_pre_topc(X2)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X2)
% 2.50/0.97      | ~ v2_pre_topc(X1)
% 2.50/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.50/0.97      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_634,c_31]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_639,plain,
% 2.50/0.97      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.50/0.97      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.50/0.97      | ~ m1_pre_topc(X0,X2)
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | v2_struct_0(X2)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ l1_pre_topc(X2)
% 2.50/0.97      | ~ v2_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X2)
% 2.50/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.50/0.97      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.50/0.97      inference(renaming,[status(thm)],[c_638]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_674,plain,
% 2.50/0.97      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.50/0.97      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.50/0.97      | ~ m1_pre_topc(X0,X2)
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | v2_struct_0(X2)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ l1_pre_topc(X2)
% 2.50/0.97      | ~ v2_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X2)
% 2.50/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.50/0.97      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.50/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_639,c_4]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_962,plain,
% 2.50/0.97      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.50/0.97      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.50/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | v2_struct_0(X2)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X2)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X2)
% 2.50/0.97      | ~ v2_pre_topc(X1)
% 2.50/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.50/0.97      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.50/0.97      | sK3 != X2
% 2.50/0.97      | sK5 != X0 ),
% 2.50/0.97      inference(resolution_lifted,[status(thm)],[c_26,c_674]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_963,plain,
% 2.50/0.97      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.50/0.97      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | v2_struct_0(sK3)
% 2.50/0.97      | v2_struct_0(sK5)
% 2.50/0.97      | ~ l1_pre_topc(X0)
% 2.50/0.97      | ~ l1_pre_topc(sK3)
% 2.50/0.97      | ~ v2_pre_topc(X0)
% 2.50/0.97      | ~ v2_pre_topc(sK3)
% 2.50/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.50/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.50/0.97      inference(unflattening,[status(thm)],[c_962]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_967,plain,
% 2.50/0.97      ( ~ v2_pre_topc(X0)
% 2.50/0.97      | ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.50/0.97      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | ~ l1_pre_topc(X0)
% 2.50/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.50/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_963,c_34,c_33,c_32,c_28]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_968,plain,
% 2.50/0.97      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.50/0.97      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | ~ l1_pre_topc(X0)
% 2.50/0.97      | ~ v2_pre_topc(X0)
% 2.50/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.50/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.50/0.97      inference(renaming,[status(thm)],[c_967]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1559,plain,
% 2.50/0.97      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.50/0.97      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.50/0.97      | v2_struct_0(X0)
% 2.50/0.97      | ~ l1_pre_topc(X0)
% 2.50/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.50/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.50/0.97      | sK2 != X0 ),
% 2.50/0.97      inference(resolution_lifted,[status(thm)],[c_968,c_36]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1560,plain,
% 2.50/0.97      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.50/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.50/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.50/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 2.50/0.97      | v2_struct_0(sK2)
% 2.50/0.97      | ~ l1_pre_topc(sK2)
% 2.50/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.50/0.97      inference(unflattening,[status(thm)],[c_1559]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1564,plain,
% 2.50/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.50/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.50/0.97      | ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.50/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_1560,c_37,c_35,c_29]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1565,plain,
% 2.50/0.97      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.50/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.50/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.50/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.50/0.97      inference(renaming,[status(thm)],[c_1564]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4620,plain,
% 2.50/0.97      ( ~ r1_tmap_1(sK3,sK2,sK4,X0_54)
% 2.50/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
% 2.50/0.97      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 2.50/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_1565]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_5734,plain,
% 2.50/0.97      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.50/0.97      | r1_tmap_1(sK3,sK2,sK4,X0_54) != iProver_top
% 2.50/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54) = iProver_top
% 2.50/0.97      | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_4620]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_5983,plain,
% 2.50/0.97      ( r1_tmap_1(sK3,sK2,sK4,X0_54) != iProver_top
% 2.50/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54) = iProver_top
% 2.50/0.97      | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top ),
% 2.50/0.97      inference(equality_resolution_simp,[status(thm)],[c_5734]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_21,negated_conjecture,
% 2.50/0.97      ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
% 2.50/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 2.50/0.97      inference(cnf_transformation,[],[f97]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4632,negated_conjecture,
% 2.50/0.97      ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
% 2.50/0.97      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_21]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_5721,plain,
% 2.50/0.97      ( r1_tmap_1(sK3,sK2,sK4,sK6) != iProver_top
% 2.50/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_4632]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_5812,plain,
% 2.50/0.97      ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
% 2.50/0.97      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
% 2.50/0.97      inference(light_normalisation,[status(thm)],[c_5721,c_4630]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_8575,plain,
% 2.50/0.97      ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
% 2.50/0.97      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 2.50/0.97      inference(superposition,[status(thm)],[c_5983,c_5812]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_9275,plain,
% 2.50/0.97      ( m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.50/0.97      | v3_pre_topc(X0_54,sK3) != iProver_top
% 2.50/0.97      | r1_tarski(X0_54,u1_struct_0(sK5)) != iProver_top
% 2.50/0.97      | r2_hidden(sK7,X0_54) != iProver_top ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_9184,c_51,c_8575]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_9276,plain,
% 2.50/0.97      ( r1_tarski(X0_54,u1_struct_0(sK5)) != iProver_top
% 2.50/0.97      | v3_pre_topc(X0_54,sK3) != iProver_top
% 2.50/0.97      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.50/0.97      | r2_hidden(sK7,X0_54) != iProver_top ),
% 2.50/0.97      inference(renaming,[status(thm)],[c_9275]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_9286,plain,
% 2.50/0.97      ( m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
% 2.50/0.97      | r1_tarski(sK1(sK3,X1_54,X0_54),u1_struct_0(sK5)) != iProver_top
% 2.50/0.97      | v3_pre_topc(sK1(sK3,X1_54,X0_54),sK3) != iProver_top
% 2.50/0.97      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.50/0.97      | r2_hidden(sK7,sK1(sK3,X1_54,X0_54)) != iProver_top ),
% 2.50/0.97      inference(superposition,[status(thm)],[c_5746,c_9276]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_10,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(cnf_transformation,[],[f72]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_243,plain,
% 2.50/0.97      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 2.50/0.97      | ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_10,c_5]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_244,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(renaming,[status(thm)],[c_243]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1763,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | sK3 != X1 ),
% 2.50/0.97      inference(resolution_lifted,[status(thm)],[c_244,c_33]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1764,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.50/0.97      | v3_pre_topc(sK1(sK3,X1,X0),sK3)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.50/0.97      | v2_struct_0(sK3)
% 2.50/0.97      | ~ l1_pre_topc(sK3) ),
% 2.50/0.97      inference(unflattening,[status(thm)],[c_1763]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1768,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.50/0.97      | v3_pre_topc(sK1(sK3,X1,X0),sK3)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_1764,c_34,c_32]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4612,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0_54,sK3,X1_54)
% 2.50/0.97      | v3_pre_topc(sK1(sK3,X1_54,X0_54),sK3)
% 2.50/0.97      | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_1768]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4719,plain,
% 2.50/0.97      ( m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
% 2.50/0.97      | v3_pre_topc(sK1(sK3,X1_54,X0_54),sK3) = iProver_top
% 2.50/0.97      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_4612]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_9505,plain,
% 2.50/0.97      ( r1_tarski(sK1(sK3,X1_54,X0_54),u1_struct_0(sK5)) != iProver_top
% 2.50/0.97      | m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
% 2.50/0.97      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.50/0.97      | r2_hidden(sK7,sK1(sK3,X1_54,X0_54)) != iProver_top ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_9286,c_4719]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_9506,plain,
% 2.50/0.97      ( m1_connsp_2(X0_54,sK3,X1_54) != iProver_top
% 2.50/0.97      | r1_tarski(sK1(sK3,X1_54,X0_54),u1_struct_0(sK5)) != iProver_top
% 2.50/0.97      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.50/0.97      | r2_hidden(sK7,sK1(sK3,X1_54,X0_54)) != iProver_top ),
% 2.50/0.97      inference(renaming,[status(thm)],[c_9505]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_9515,plain,
% 2.50/0.97      ( m1_connsp_2(u1_struct_0(sK5),sK3,X0_54) != iProver_top
% 2.50/0.97      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 2.50/0.97      | r2_hidden(sK7,sK1(sK3,X0_54,u1_struct_0(sK5))) != iProver_top ),
% 2.50/0.97      inference(superposition,[status(thm)],[c_5743,c_9506]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_9523,plain,
% 2.50/0.97      ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7) != iProver_top
% 2.50/0.97      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top ),
% 2.50/0.97      inference(superposition,[status(thm)],[c_7425,c_9515]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1,plain,
% 2.50/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.50/0.97      | ~ r2_hidden(X2,X0)
% 2.50/0.97      | ~ v1_xboole_0(X1) ),
% 2.50/0.97      inference(cnf_transformation,[],[f61]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4633,plain,
% 2.50/0.97      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 2.50/0.97      | ~ r2_hidden(X2_54,X0_54)
% 2.50/0.97      | ~ v1_xboole_0(X1_54) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_1]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_6435,plain,
% 2.50/0.97      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.50/0.97      | ~ r2_hidden(X1_54,X0_54)
% 2.50/0.97      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 2.50/0.97      inference(instantiation,[status(thm)],[c_4633]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_6758,plain,
% 2.50/0.97      ( ~ m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 2.50/0.97      | ~ r2_hidden(X0_54,sK0(sK5,sK7))
% 2.50/0.97      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 2.50/0.97      inference(instantiation,[status(thm)],[c_6435]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_7722,plain,
% 2.50/0.97      ( ~ m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 2.50/0.97      | ~ r2_hidden(sK7,sK0(sK5,sK7))
% 2.50/0.97      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 2.50/0.97      inference(instantiation,[status(thm)],[c_6758]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_7723,plain,
% 2.50/0.97      ( m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 2.50/0.97      | r2_hidden(sK7,sK0(sK5,sK7)) != iProver_top
% 2.50/0.97      | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_7722]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_7,plain,
% 2.50/0.97      ( m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | ~ v3_pre_topc(X0,X1)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.97      | ~ r2_hidden(X2,X0)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1) ),
% 2.50/0.97      inference(cnf_transformation,[],[f67]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1847,plain,
% 2.50/0.97      ( m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | ~ v3_pre_topc(X0,X1)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.97      | ~ r2_hidden(X2,X0)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | sK3 != X1 ),
% 2.50/0.97      inference(resolution_lifted,[status(thm)],[c_7,c_33]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1848,plain,
% 2.50/0.97      ( m1_connsp_2(X0,sK3,X1)
% 2.50/0.97      | ~ v3_pre_topc(X0,sK3)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.50/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.50/0.97      | ~ r2_hidden(X1,X0)
% 2.50/0.97      | v2_struct_0(sK3)
% 2.50/0.97      | ~ l1_pre_topc(sK3) ),
% 2.50/0.97      inference(unflattening,[status(thm)],[c_1847]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1852,plain,
% 2.50/0.97      ( m1_connsp_2(X0,sK3,X1)
% 2.50/0.97      | ~ v3_pre_topc(X0,sK3)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.50/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.50/0.97      | ~ r2_hidden(X1,X0) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_1848,c_34,c_32]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4608,plain,
% 2.50/0.97      ( m1_connsp_2(X0_54,sK3,X1_54)
% 2.50/0.97      | ~ v3_pre_topc(X0_54,sK3)
% 2.50/0.97      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 2.50/0.97      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.50/0.97      | ~ r2_hidden(X1_54,X0_54) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_1852]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_6223,plain,
% 2.50/0.97      ( m1_connsp_2(u1_struct_0(sK5),sK3,X0_54)
% 2.50/0.97      | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
% 2.50/0.97      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.50/0.97      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.50/0.97      | ~ r2_hidden(X0_54,u1_struct_0(sK5)) ),
% 2.50/0.97      inference(instantiation,[status(thm)],[c_4608]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_6752,plain,
% 2.50/0.97      ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
% 2.50/0.97      | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
% 2.50/0.97      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.50/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.50/0.97      | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
% 2.50/0.97      inference(instantiation,[status(thm)],[c_6223]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_6753,plain,
% 2.50/0.97      ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7) = iProver_top
% 2.50/0.97      | v3_pre_topc(u1_struct_0(sK5),sK3) != iProver_top
% 2.50/0.97      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.50/0.97      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.50/0.97      | r2_hidden(sK7,u1_struct_0(sK5)) != iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_6752]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_2,plain,
% 2.50/0.97      ( ~ m1_pre_topc(X0,X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | ~ v2_pre_topc(X1)
% 2.50/0.97      | v2_pre_topc(X0) ),
% 2.50/0.97      inference(cnf_transformation,[],[f62]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_900,plain,
% 2.50/0.97      ( ~ l1_pre_topc(X0)
% 2.50/0.97      | ~ v2_pre_topc(X0)
% 2.50/0.97      | v2_pre_topc(X1)
% 2.50/0.97      | sK3 != X0
% 2.50/0.97      | sK5 != X1 ),
% 2.50/0.97      inference(resolution_lifted,[status(thm)],[c_2,c_26]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_901,plain,
% 2.50/0.97      ( ~ l1_pre_topc(sK3) | ~ v2_pre_topc(sK3) | v2_pre_topc(sK5) ),
% 2.50/0.97      inference(unflattening,[status(thm)],[c_900]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_903,plain,
% 2.50/0.97      ( v2_pre_topc(sK5) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_901,c_33,c_32]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_2069,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.97      | r2_hidden(X2,X0)
% 2.50/0.97      | v2_struct_0(X1)
% 2.50/0.97      | ~ l1_pre_topc(X1)
% 2.50/0.97      | sK5 != X1 ),
% 2.50/0.97      inference(resolution_lifted,[status(thm)],[c_258,c_903]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_2070,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,sK5,X1)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.50/0.97      | r2_hidden(X1,X0)
% 2.50/0.97      | v2_struct_0(sK5)
% 2.50/0.97      | ~ l1_pre_topc(sK5) ),
% 2.50/0.97      inference(unflattening,[status(thm)],[c_2069]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_3,plain,
% 2.50/0.97      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.50/0.97      inference(cnf_transformation,[],[f63]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_889,plain,
% 2.50/0.97      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK3 != X0 | sK5 != X1 ),
% 2.50/0.97      inference(resolution_lifted,[status(thm)],[c_3,c_26]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_890,plain,
% 2.50/0.97      ( ~ l1_pre_topc(sK3) | l1_pre_topc(sK5) ),
% 2.50/0.97      inference(unflattening,[status(thm)],[c_889]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_2074,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0,sK5,X1)
% 2.50/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.50/0.97      | r2_hidden(X1,X0) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_2070,c_32,c_28,c_890]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4598,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0_54,sK5,X1_54)
% 2.50/0.97      | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
% 2.50/0.97      | r2_hidden(X1_54,X0_54) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_2074]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_6258,plain,
% 2.50/0.97      ( ~ m1_connsp_2(X0_54,sK5,sK7)
% 2.50/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 2.50/0.97      | r2_hidden(sK7,X0_54) ),
% 2.50/0.97      inference(instantiation,[status(thm)],[c_4598]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_6504,plain,
% 2.50/0.97      ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
% 2.50/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 2.50/0.97      | r2_hidden(sK7,sK0(sK5,sK7)) ),
% 2.50/0.97      inference(instantiation,[status(thm)],[c_6258]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_6505,plain,
% 2.50/0.97      ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) != iProver_top
% 2.50/0.97      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
% 2.50/0.97      | r2_hidden(sK7,sK0(sK5,sK7)) = iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_6504]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_2222,plain,
% 2.50/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.50/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.50/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.98      | v2_struct_0(X1)
% 2.50/0.98      | ~ l1_pre_topc(X1)
% 2.50/0.98      | sK5 != X1 ),
% 2.50/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_903]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_2223,plain,
% 2.50/0.98      ( ~ m1_connsp_2(X0,sK5,X1)
% 2.50/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.50/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.50/0.98      | v2_struct_0(sK5)
% 2.50/0.98      | ~ l1_pre_topc(sK5) ),
% 2.50/0.98      inference(unflattening,[status(thm)],[c_2222]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_2227,plain,
% 2.50/0.98      ( ~ m1_connsp_2(X0,sK5,X1)
% 2.50/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.50/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 2.50/0.98      inference(global_propositional_subsumption,
% 2.50/0.98                [status(thm)],
% 2.50/0.98                [c_2223,c_32,c_28,c_890]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_4591,plain,
% 2.50/0.98      ( ~ m1_connsp_2(X0_54,sK5,X1_54)
% 2.50/0.98      | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
% 2.50/0.98      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 2.50/0.98      inference(subtyping,[status(esa)],[c_2227]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_6234,plain,
% 2.50/0.98      ( ~ m1_connsp_2(X0_54,sK5,sK7)
% 2.50/0.98      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.50/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 2.50/0.98      inference(instantiation,[status(thm)],[c_4591]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_6492,plain,
% 2.50/0.98      ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
% 2.50/0.98      | m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 2.50/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 2.50/0.98      inference(instantiation,[status(thm)],[c_6234]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_6493,plain,
% 2.50/0.98      ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) != iProver_top
% 2.50/0.98      | m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 2.50/0.98      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 2.50/0.98      inference(predicate_to_equality,[status(thm)],[c_6492]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_4629,negated_conjecture,
% 2.50/0.98      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 2.50/0.98      inference(subtyping,[status(esa)],[c_24]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_5723,plain,
% 2.50/0.98      ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
% 2.50/0.98      inference(predicate_to_equality,[status(thm)],[c_4629]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_0,plain,
% 2.50/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.50/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_4634,plain,
% 2.50/0.98      ( ~ m1_subset_1(X0_54,X1_54)
% 2.50/0.98      | r2_hidden(X0_54,X1_54)
% 2.50/0.98      | v1_xboole_0(X1_54) ),
% 2.50/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_5719,plain,
% 2.50/0.98      ( m1_subset_1(X0_54,X1_54) != iProver_top
% 2.50/0.98      | r2_hidden(X0_54,X1_54) = iProver_top
% 2.50/0.98      | v1_xboole_0(X1_54) = iProver_top ),
% 2.50/0.98      inference(predicate_to_equality,[status(thm)],[c_4634]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_6282,plain,
% 2.50/0.98      ( r2_hidden(sK7,u1_struct_0(sK5)) = iProver_top
% 2.50/0.98      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 2.50/0.98      inference(superposition,[status(thm)],[c_5723,c_5719]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_6,plain,
% 2.50/0.98      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 2.50/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.50/0.98      | v2_struct_0(X0)
% 2.50/0.98      | ~ l1_pre_topc(X0)
% 2.50/0.98      | ~ v2_pre_topc(X0) ),
% 2.50/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_1703,plain,
% 2.50/0.98      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 2.50/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.50/0.98      | v2_struct_0(X0)
% 2.50/0.98      | ~ l1_pre_topc(X0)
% 2.50/0.98      | sK5 != X0 ),
% 2.50/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_903]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_1704,plain,
% 2.50/0.98      ( m1_connsp_2(sK0(sK5,X0),sK5,X0)
% 2.50/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.50/0.98      | v2_struct_0(sK5)
% 2.50/0.98      | ~ l1_pre_topc(sK5) ),
% 2.50/0.98      inference(unflattening,[status(thm)],[c_1703]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_1708,plain,
% 2.50/0.98      ( m1_connsp_2(sK0(sK5,X0),sK5,X0)
% 2.50/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 2.50/0.98      inference(global_propositional_subsumption,
% 2.50/0.98                [status(thm)],
% 2.50/0.98                [c_1704,c_32,c_28,c_890]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_4615,plain,
% 2.50/0.98      ( m1_connsp_2(sK0(sK5,X0_54),sK5,X0_54)
% 2.50/0.98      | ~ m1_subset_1(X0_54,u1_struct_0(sK5)) ),
% 2.50/0.98      inference(subtyping,[status(esa)],[c_1708]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_6228,plain,
% 2.50/0.98      ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
% 2.50/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 2.50/0.98      inference(instantiation,[status(thm)],[c_4615]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_6229,plain,
% 2.50/0.98      ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) = iProver_top
% 2.50/0.98      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 2.50/0.98      inference(predicate_to_equality,[status(thm)],[c_6228]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_25,negated_conjecture,
% 2.50/0.98      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.50/0.98      inference(cnf_transformation,[],[f93]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_4628,negated_conjecture,
% 2.50/0.98      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.50/0.98      inference(subtyping,[status(esa)],[c_25]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_5724,plain,
% 2.50/0.98      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.50/0.98      inference(predicate_to_equality,[status(thm)],[c_4628]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_5770,plain,
% 2.50/0.98      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.50/0.98      inference(light_normalisation,[status(thm)],[c_5724,c_4630]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_17,plain,
% 2.50/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.50/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.98      | ~ l1_pre_topc(X1) ),
% 2.50/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_860,plain,
% 2.50/0.98      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.98      | ~ l1_pre_topc(X1)
% 2.50/0.98      | sK3 != X1
% 2.50/0.98      | sK5 != X0 ),
% 2.50/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_861,plain,
% 2.50/0.98      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.50/0.98      | ~ l1_pre_topc(sK3) ),
% 2.50/0.98      inference(unflattening,[status(thm)],[c_860]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_862,plain,
% 2.50/0.98      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.50/0.98      | l1_pre_topc(sK3) != iProver_top ),
% 2.50/0.98      inference(predicate_to_equality,[status(thm)],[c_861]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_16,plain,
% 2.50/0.98      ( ~ v1_tsep_1(X0,X1)
% 2.50/0.98      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.50/0.98      | ~ m1_pre_topc(X0,X1)
% 2.50/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.98      | ~ l1_pre_topc(X1)
% 2.50/0.98      | ~ v2_pre_topc(X1) ),
% 2.50/0.98      inference(cnf_transformation,[],[f100]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_208,plain,
% 2.50/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.50/0.98      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.50/0.98      | ~ v1_tsep_1(X0,X1)
% 2.50/0.98      | ~ l1_pre_topc(X1)
% 2.50/0.98      | ~ v2_pre_topc(X1) ),
% 2.50/0.98      inference(global_propositional_subsumption,
% 2.50/0.98                [status(thm)],
% 2.50/0.98                [c_16,c_17]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_209,plain,
% 2.50/0.98      ( ~ v1_tsep_1(X0,X1)
% 2.50/0.98      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.50/0.98      | ~ m1_pre_topc(X0,X1)
% 2.50/0.98      | ~ l1_pre_topc(X1)
% 2.50/0.98      | ~ v2_pre_topc(X1) ),
% 2.50/0.98      inference(renaming,[status(thm)],[c_208]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_27,negated_conjecture,
% 2.50/0.98      ( v1_tsep_1(sK5,sK3) ),
% 2.50/0.98      inference(cnf_transformation,[],[f91]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_567,plain,
% 2.50/0.98      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.50/0.98      | ~ m1_pre_topc(X0,X1)
% 2.50/0.98      | ~ l1_pre_topc(X1)
% 2.50/0.98      | ~ v2_pre_topc(X1)
% 2.50/0.98      | sK3 != X1
% 2.50/0.98      | sK5 != X0 ),
% 2.50/0.98      inference(resolution_lifted,[status(thm)],[c_209,c_27]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_568,plain,
% 2.50/0.98      ( v3_pre_topc(u1_struct_0(sK5),sK3)
% 2.50/0.98      | ~ m1_pre_topc(sK5,sK3)
% 2.50/0.98      | ~ l1_pre_topc(sK3)
% 2.50/0.98      | ~ v2_pre_topc(sK3) ),
% 2.50/0.98      inference(unflattening,[status(thm)],[c_567]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_569,plain,
% 2.50/0.98      ( v3_pre_topc(u1_struct_0(sK5),sK3) = iProver_top
% 2.50/0.98      | m1_pre_topc(sK5,sK3) != iProver_top
% 2.50/0.98      | l1_pre_topc(sK3) != iProver_top
% 2.50/0.98      | v2_pre_topc(sK3) != iProver_top ),
% 2.50/0.98      inference(predicate_to_equality,[status(thm)],[c_568]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_49,plain,
% 2.50/0.98      ( m1_pre_topc(sK5,sK3) = iProver_top ),
% 2.50/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_43,plain,
% 2.50/0.98      ( l1_pre_topc(sK3) = iProver_top ),
% 2.50/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_42,plain,
% 2.50/0.98      ( v2_pre_topc(sK3) = iProver_top ),
% 2.50/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(contradiction,plain,
% 2.50/0.98      ( $false ),
% 2.50/0.98      inference(minisat,
% 2.50/0.98                [status(thm)],
% 2.50/0.98                [c_9523,c_7723,c_6753,c_6505,c_6493,c_6282,c_6229,c_5770,
% 2.50/0.98                 c_862,c_569,c_51,c_49,c_43,c_42]) ).
% 2.50/0.98  
% 2.50/0.98  
% 2.50/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.50/0.98  
% 2.50/0.98  ------                               Statistics
% 2.50/0.98  
% 2.50/0.98  ------ General
% 2.50/0.98  
% 2.50/0.98  abstr_ref_over_cycles:                  0
% 2.50/0.98  abstr_ref_under_cycles:                 0
% 2.50/0.98  gc_basic_clause_elim:                   0
% 2.50/0.98  forced_gc_time:                         0
% 2.50/0.98  parsing_time:                           0.012
% 2.50/0.98  unif_index_cands_time:                  0.
% 2.50/0.98  unif_index_add_time:                    0.
% 2.50/0.98  orderings_time:                         0.
% 2.50/0.98  out_proof_time:                         0.015
% 2.50/0.98  total_time:                             0.262
% 2.50/0.98  num_of_symbols:                         63
% 2.50/0.98  num_of_terms:                           5694
% 2.50/0.98  
% 2.50/0.98  ------ Preprocessing
% 2.50/0.98  
% 2.50/0.98  num_of_splits:                          4
% 2.50/0.98  num_of_split_atoms:                     4
% 2.50/0.98  num_of_reused_defs:                     0
% 2.50/0.98  num_eq_ax_congr_red:                    26
% 2.50/0.98  num_of_sem_filtered_clauses:            1
% 2.50/0.98  num_of_subtypes:                        2
% 2.50/0.98  monotx_restored_types:                  0
% 2.50/0.98  sat_num_of_epr_types:                   0
% 2.50/0.98  sat_num_of_non_cyclic_types:            0
% 2.50/0.98  sat_guarded_non_collapsed_types:        0
% 2.50/0.98  num_pure_diseq_elim:                    0
% 2.50/0.98  simp_replaced_by:                       0
% 2.50/0.98  res_preprocessed:                       156
% 2.50/0.98  prep_upred:                             0
% 2.50/0.98  prep_unflattend:                        149
% 2.50/0.98  smt_new_axioms:                         0
% 2.50/0.98  pred_elim_cands:                        14
% 2.50/0.98  pred_elim:                              7
% 2.50/0.98  pred_elim_cl:                           -7
% 2.50/0.98  pred_elim_cycles:                       17
% 2.50/0.98  merged_defs:                            6
% 2.50/0.98  merged_defs_ncl:                        0
% 2.50/0.98  bin_hyper_res:                          6
% 2.50/0.98  prep_cycles:                            3
% 2.50/0.98  pred_elim_time:                         0.097
% 2.50/0.98  splitting_time:                         0.
% 2.50/0.98  sem_filter_time:                        0.
% 2.50/0.98  monotx_time:                            0.
% 2.50/0.98  subtype_inf_time:                       0.
% 2.50/0.98  
% 2.50/0.98  ------ Problem properties
% 2.50/0.98  
% 2.50/0.98  clauses:                                48
% 2.50/0.98  conjectures:                            6
% 2.50/0.98  epr:                                    2
% 2.50/0.98  horn:                                   46
% 2.50/0.98  ground:                                 12
% 2.50/0.98  unary:                                  6
% 2.50/0.98  binary:                                 6
% 2.50/0.98  lits:                                   150
% 2.50/0.98  lits_eq:                                7
% 2.50/0.98  fd_pure:                                0
% 2.50/0.98  fd_pseudo:                              0
% 2.50/0.98  fd_cond:                                0
% 2.50/0.98  fd_pseudo_cond:                         0
% 2.50/0.98  ac_symbols:                             0
% 2.50/0.98  
% 2.50/0.98  ------ Propositional Solver
% 2.50/0.98  
% 2.50/0.98  prop_solver_calls:                      24
% 2.50/0.98  prop_fast_solver_calls:                 2645
% 2.50/0.98  smt_solver_calls:                       0
% 2.50/0.98  smt_fast_solver_calls:                  0
% 2.50/0.98  prop_num_of_clauses:                    2628
% 2.50/0.98  prop_preprocess_simplified:             7346
% 2.50/0.98  prop_fo_subsumed:                       140
% 2.50/0.98  prop_solver_time:                       0.
% 2.50/0.98  smt_solver_time:                        0.
% 2.50/0.98  smt_fast_solver_time:                   0.
% 2.50/0.98  prop_fast_solver_time:                  0.
% 2.50/0.98  prop_unsat_core_time:                   0.
% 2.50/0.98  
% 2.50/0.98  ------ QBF
% 2.50/0.98  
% 2.50/0.98  qbf_q_res:                              0
% 2.50/0.98  qbf_num_tautologies:                    0
% 2.50/0.98  qbf_prep_cycles:                        0
% 2.50/0.98  
% 2.50/0.98  ------ BMC1
% 2.50/0.98  
% 2.50/0.98  bmc1_current_bound:                     -1
% 2.50/0.98  bmc1_last_solved_bound:                 -1
% 2.50/0.98  bmc1_unsat_core_size:                   -1
% 2.50/0.98  bmc1_unsat_core_parents_size:           -1
% 2.50/0.98  bmc1_merge_next_fun:                    0
% 2.50/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.50/0.98  
% 2.50/0.98  ------ Instantiation
% 2.50/0.98  
% 2.50/0.98  inst_num_of_clauses:                    597
% 2.50/0.98  inst_num_in_passive:                    66
% 2.50/0.98  inst_num_in_active:                     420
% 2.50/0.98  inst_num_in_unprocessed:                111
% 2.50/0.98  inst_num_of_loops:                      440
% 2.50/0.98  inst_num_of_learning_restarts:          0
% 2.50/0.98  inst_num_moves_active_passive:          17
% 2.50/0.98  inst_lit_activity:                      0
% 2.50/0.98  inst_lit_activity_moves:                0
% 2.50/0.98  inst_num_tautologies:                   0
% 2.50/0.98  inst_num_prop_implied:                  0
% 2.50/0.98  inst_num_existing_simplified:           0
% 2.50/0.98  inst_num_eq_res_simplified:             0
% 2.50/0.98  inst_num_child_elim:                    0
% 2.50/0.98  inst_num_of_dismatching_blockings:      16
% 2.50/0.98  inst_num_of_non_proper_insts:           477
% 2.50/0.98  inst_num_of_duplicates:                 0
% 2.50/0.98  inst_inst_num_from_inst_to_res:         0
% 2.50/0.98  inst_dismatching_checking_time:         0.
% 2.50/0.98  
% 2.50/0.98  ------ Resolution
% 2.50/0.98  
% 2.50/0.98  res_num_of_clauses:                     0
% 2.50/0.98  res_num_in_passive:                     0
% 2.50/0.98  res_num_in_active:                      0
% 2.50/0.98  res_num_of_loops:                       159
% 2.50/0.98  res_forward_subset_subsumed:            43
% 2.50/0.98  res_backward_subset_subsumed:           0
% 2.50/0.98  res_forward_subsumed:                   0
% 2.50/0.98  res_backward_subsumed:                  0
% 2.50/0.98  res_forward_subsumption_resolution:     14
% 2.50/0.98  res_backward_subsumption_resolution:    0
% 2.50/0.98  res_clause_to_clause_subsumption:       475
% 2.50/0.98  res_orphan_elimination:                 0
% 2.50/0.98  res_tautology_del:                      80
% 2.50/0.98  res_num_eq_res_simplified:              2
% 2.50/0.98  res_num_sel_changes:                    0
% 2.50/0.98  res_moves_from_active_to_pass:          0
% 2.50/0.98  
% 2.50/0.98  ------ Superposition
% 2.50/0.98  
% 2.50/0.98  sup_time_total:                         0.
% 2.50/0.98  sup_time_generating:                    0.
% 2.50/0.98  sup_time_sim_full:                      0.
% 2.50/0.98  sup_time_sim_immed:                     0.
% 2.50/0.98  
% 2.50/0.98  sup_num_of_clauses:                     91
% 2.50/0.98  sup_num_in_active:                      86
% 2.50/0.98  sup_num_in_passive:                     5
% 2.50/0.98  sup_num_of_loops:                       87
% 2.50/0.98  sup_fw_superposition:                   29
% 2.50/0.98  sup_bw_superposition:                   36
% 2.50/0.98  sup_immediate_simplified:               7
% 2.50/0.98  sup_given_eliminated:                   0
% 2.50/0.98  comparisons_done:                       0
% 2.50/0.98  comparisons_avoided:                    0
% 2.50/0.98  
% 2.50/0.98  ------ Simplifications
% 2.50/0.98  
% 2.50/0.98  
% 2.50/0.98  sim_fw_subset_subsumed:                 2
% 2.50/0.98  sim_bw_subset_subsumed:                 3
% 2.50/0.98  sim_fw_subsumed:                        6
% 2.50/0.98  sim_bw_subsumed:                        0
% 2.50/0.98  sim_fw_subsumption_res:                 0
% 2.50/0.98  sim_bw_subsumption_res:                 0
% 2.50/0.98  sim_tautology_del:                      9
% 2.50/0.98  sim_eq_tautology_del:                   0
% 2.50/0.98  sim_eq_res_simp:                        2
% 2.50/0.98  sim_fw_demodulated:                     0
% 2.50/0.98  sim_bw_demodulated:                     0
% 2.50/0.98  sim_light_normalised:                   3
% 2.50/0.98  sim_joinable_taut:                      0
% 2.50/0.98  sim_joinable_simp:                      0
% 2.50/0.98  sim_ac_normalised:                      0
% 2.50/0.98  sim_smt_subsumption:                    0
% 2.50/0.98  
%------------------------------------------------------------------------------
