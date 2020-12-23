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
% DateTime   : Thu Dec  3 12:22:46 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :  193 (1071 expanded)
%              Number of clauses        :  109 ( 178 expanded)
%              Number of leaves         :   20 ( 420 expanded)
%              Depth                    :   35
%              Number of atoms          : 1497 (16737 expanded)
%              Number of equality atoms :  131 (1199 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   38 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( r1_tarski(X3,X1)
                      & m1_connsp_2(X3,X0,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( r1_tarski(X5,X1)
                      & m1_connsp_2(X5,X0,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f35])).

fof(f38,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK1(X0,X1,X4),X1)
        & m1_connsp_2(sK1(X0,X1,X4),X0,X4)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X1)
              | ~ m1_connsp_2(X3,X0,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_tarski(X3,X1)
            | ~ m1_connsp_2(X3,X0,sK0(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,sK0(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ( r1_tarski(sK1(X0,X1,X4),X1)
                    & m1_connsp_2(sK1(X0,X1,X4),X0,X4)
                    & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X4),X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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
    inference(negated_conjecture,[],[f12])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f44,f50,f49,f48,f47,f46,f45])).

fof(f75,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f74,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    v1_tsep_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f51])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( m1_connsp_2(sK1(X0,X1,X4),X0,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f92,plain,(
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
    inference(equality_resolution,[],[f70])).

fof(f78,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f71,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f73,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
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
    inference(equality_resolution,[],[f69])).

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
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,(
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
    inference(equality_resolution,[],[f68])).

fof(f87,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ r1_tmap_1(sK3,sK2,sK4,sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | r1_tmap_1(sK3,sK2,sK4,sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_9,plain,
    ( r1_tarski(sK1(X0,X1,X2),X1)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1788,plain,
    ( r1_tarski(sK1(X0,X1,X2),X1)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_31])).

cnf(c_1789,plain,
    ( r1_tarski(sK1(sK3,X0,X1),X0)
    | ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X1,X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1788])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1793,plain,
    ( r1_tarski(sK1(sK3,X0,X1),X0)
    | ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1789,c_32,c_30])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_462,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_917,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_24])).

cnf(c_918,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_917])).

cnf(c_920,plain,
    ( l1_pre_topc(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_918,c_30])).

cnf(c_2172,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_462,c_920])).

cnf(c_2173,plain,
    ( v2_struct_0(sK5)
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_2172])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2175,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2173,c_26])).

cnf(c_2213,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | u1_struct_0(sK5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2175])).

cnf(c_2214,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_2213])).

cnf(c_3178,plain,
    ( r1_tarski(sK1(sK3,X0,X1),X0)
    | ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | X2 != X1
    | u1_struct_0(sK5) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1793,c_2214])).

cnf(c_3179,plain,
    ( r1_tarski(sK1(sK3,u1_struct_0(sK5),X0),u1_struct_0(sK5))
    | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_3178])).

cnf(c_14,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_198,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_15])).

cnf(c_199,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_198])).

cnf(c_25,negated_conjecture,
    ( v1_tsep_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_503,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_199,c_25])).

cnf(c_504,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ m1_pre_topc(sK5,sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_888,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_889,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_888])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_899,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | sK3 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_900,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_899])).

cnf(c_904,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_900,c_32,c_30,c_26])).

cnf(c_905,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_904])).

cnf(c_3183,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_tarski(sK1(sK3,u1_struct_0(sK5),X0),u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3179,c_32,c_31,c_30,c_26,c_24,c_504,c_889,c_900])).

cnf(c_3184,plain,
    ( r1_tarski(sK1(sK3,u1_struct_0(sK5),X0),u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_3183])).

cnf(c_10,plain,
    ( m1_connsp_2(sK1(X0,X1,X2),X0,X2)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_17,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_674,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_675,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_679,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_connsp_2(X4,X2,X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_675,c_29])).

cnf(c_680,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_679])).

cnf(c_5,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_721,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_680,c_4,c_5])).

cnf(c_928,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_721])).

cnf(c_929,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_928])).

cnf(c_933,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_929,c_32,c_31,c_30,c_26])).

cnf(c_934,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_933])).

cnf(c_1168,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ v3_pre_topc(X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X5,X3)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | X1 != X5
    | sK1(X4,X3,X5) != X2
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK3 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_934])).

cnf(c_1169,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X1,X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1168])).

cnf(c_1173,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(X2,sK3)
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | r1_tmap_1(sK3,X0,sK4,X1)
    | v2_struct_0(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1169,c_32,c_31,c_30])).

cnf(c_1174,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X1,X2)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1173])).

cnf(c_1203,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X1,X2)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1174,c_905])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1815,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X1,X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1203,c_34])).

cnf(c_1816,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
    | ~ v3_pre_topc(X1,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ r2_hidden(X0,X1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1815])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1820,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(X1,sK3)
    | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r2_hidden(X0,X1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1816,c_35,c_33,c_27])).

cnf(c_1821,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
    | ~ v3_pre_topc(X1,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X0,X1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1820])).

cnf(c_2699,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
    | ~ v3_pre_topc(X1,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | X2 != X0
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1821,c_2214])).

cnf(c_2700,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tarski(sK1(sK3,u1_struct_0(sK5),X0),u1_struct_0(sK5))
    | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_2699])).

cnf(c_2704,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tarski(sK1(sK3,u1_struct_0(sK5),X0),u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2700,c_31,c_30,c_24,c_504,c_889])).

cnf(c_2705,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tarski(sK1(sK3,u1_struct_0(sK5),X0),u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_2704])).

cnf(c_3194,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3184,c_2705])).

cnf(c_5365,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_56)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_56)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_3194])).

cnf(c_6374,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_5365])).

cnf(c_6375,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6374])).

cnf(c_18,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_16,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_190,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_16])).

cnf(c_191,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_190])).

cnf(c_617,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_191,c_28])).

cnf(c_618,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_622,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_618,c_29])).

cnf(c_623,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_622])).

cnf(c_658,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_623,c_4])).

cnf(c_973,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_658])).

cnf(c_974,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_973])).

cnf(c_978,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_974,c_32,c_31,c_30,c_26])).

cnf(c_979,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_978])).

cnf(c_1877,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_979,c_34])).

cnf(c_1878,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1877])).

cnf(c_1882,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1878,c_35,c_33,c_27])).

cnf(c_1883,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1882])).

cnf(c_4345,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1883])).

cnf(c_5364,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0_56)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_56)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_4345])).

cnf(c_6368,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_5364])).

cnf(c_6369,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6368])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_5389,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_6077,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK6) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5389])).

cnf(c_21,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_5387,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_6138,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6077,c_5387])).

cnf(c_20,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK6)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_5388,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK6)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_6078,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK6) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5388])).

cnf(c_6133,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6078,c_5387])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_49,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6375,c_6369,c_6138,c_6133,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:44:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 2.00/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.01  
% 2.00/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.00/1.01  
% 2.00/1.01  ------  iProver source info
% 2.00/1.01  
% 2.00/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.00/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.00/1.01  git: non_committed_changes: false
% 2.00/1.01  git: last_make_outside_of_git: false
% 2.00/1.01  
% 2.00/1.01  ------ 
% 2.00/1.01  
% 2.00/1.01  ------ Input Options
% 2.00/1.01  
% 2.00/1.01  --out_options                           all
% 2.00/1.01  --tptp_safe_out                         true
% 2.00/1.01  --problem_path                          ""
% 2.00/1.01  --include_path                          ""
% 2.00/1.01  --clausifier                            res/vclausify_rel
% 2.00/1.01  --clausifier_options                    --mode clausify
% 2.00/1.01  --stdin                                 false
% 2.00/1.01  --stats_out                             all
% 2.00/1.01  
% 2.00/1.01  ------ General Options
% 2.00/1.01  
% 2.00/1.01  --fof                                   false
% 2.00/1.01  --time_out_real                         305.
% 2.00/1.01  --time_out_virtual                      -1.
% 2.00/1.01  --symbol_type_check                     false
% 2.00/1.01  --clausify_out                          false
% 2.00/1.01  --sig_cnt_out                           false
% 2.00/1.01  --trig_cnt_out                          false
% 2.00/1.01  --trig_cnt_out_tolerance                1.
% 2.00/1.01  --trig_cnt_out_sk_spl                   false
% 2.00/1.01  --abstr_cl_out                          false
% 2.00/1.01  
% 2.00/1.01  ------ Global Options
% 2.00/1.01  
% 2.00/1.01  --schedule                              default
% 2.00/1.01  --add_important_lit                     false
% 2.00/1.01  --prop_solver_per_cl                    1000
% 2.00/1.01  --min_unsat_core                        false
% 2.00/1.01  --soft_assumptions                      false
% 2.00/1.01  --soft_lemma_size                       3
% 2.00/1.01  --prop_impl_unit_size                   0
% 2.00/1.01  --prop_impl_unit                        []
% 2.00/1.01  --share_sel_clauses                     true
% 2.00/1.01  --reset_solvers                         false
% 2.00/1.01  --bc_imp_inh                            [conj_cone]
% 2.00/1.01  --conj_cone_tolerance                   3.
% 2.00/1.01  --extra_neg_conj                        none
% 2.00/1.01  --large_theory_mode                     true
% 2.00/1.01  --prolific_symb_bound                   200
% 2.00/1.01  --lt_threshold                          2000
% 2.00/1.01  --clause_weak_htbl                      true
% 2.00/1.01  --gc_record_bc_elim                     false
% 2.00/1.01  
% 2.00/1.01  ------ Preprocessing Options
% 2.00/1.01  
% 2.00/1.01  --preprocessing_flag                    true
% 2.00/1.01  --time_out_prep_mult                    0.1
% 2.00/1.01  --splitting_mode                        input
% 2.00/1.01  --splitting_grd                         true
% 2.00/1.01  --splitting_cvd                         false
% 2.00/1.01  --splitting_cvd_svl                     false
% 2.00/1.01  --splitting_nvd                         32
% 2.00/1.01  --sub_typing                            true
% 2.00/1.01  --prep_gs_sim                           true
% 2.00/1.01  --prep_unflatten                        true
% 2.00/1.01  --prep_res_sim                          true
% 2.00/1.01  --prep_upred                            true
% 2.00/1.01  --prep_sem_filter                       exhaustive
% 2.00/1.01  --prep_sem_filter_out                   false
% 2.00/1.01  --pred_elim                             true
% 2.00/1.01  --res_sim_input                         true
% 2.00/1.01  --eq_ax_congr_red                       true
% 2.00/1.01  --pure_diseq_elim                       true
% 2.00/1.01  --brand_transform                       false
% 2.00/1.01  --non_eq_to_eq                          false
% 2.00/1.01  --prep_def_merge                        true
% 2.00/1.01  --prep_def_merge_prop_impl              false
% 2.00/1.01  --prep_def_merge_mbd                    true
% 2.00/1.01  --prep_def_merge_tr_red                 false
% 2.00/1.01  --prep_def_merge_tr_cl                  false
% 2.00/1.01  --smt_preprocessing                     true
% 2.00/1.01  --smt_ac_axioms                         fast
% 2.00/1.01  --preprocessed_out                      false
% 2.00/1.01  --preprocessed_stats                    false
% 2.00/1.01  
% 2.00/1.01  ------ Abstraction refinement Options
% 2.00/1.01  
% 2.00/1.01  --abstr_ref                             []
% 2.00/1.01  --abstr_ref_prep                        false
% 2.00/1.01  --abstr_ref_until_sat                   false
% 2.00/1.01  --abstr_ref_sig_restrict                funpre
% 2.00/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.00/1.01  --abstr_ref_under                       []
% 2.00/1.01  
% 2.00/1.01  ------ SAT Options
% 2.00/1.01  
% 2.00/1.01  --sat_mode                              false
% 2.00/1.01  --sat_fm_restart_options                ""
% 2.00/1.01  --sat_gr_def                            false
% 2.00/1.01  --sat_epr_types                         true
% 2.00/1.01  --sat_non_cyclic_types                  false
% 2.00/1.01  --sat_finite_models                     false
% 2.00/1.01  --sat_fm_lemmas                         false
% 2.00/1.01  --sat_fm_prep                           false
% 2.00/1.01  --sat_fm_uc_incr                        true
% 2.00/1.01  --sat_out_model                         small
% 2.00/1.01  --sat_out_clauses                       false
% 2.00/1.01  
% 2.00/1.01  ------ QBF Options
% 2.00/1.01  
% 2.00/1.01  --qbf_mode                              false
% 2.00/1.01  --qbf_elim_univ                         false
% 2.00/1.01  --qbf_dom_inst                          none
% 2.00/1.01  --qbf_dom_pre_inst                      false
% 2.00/1.01  --qbf_sk_in                             false
% 2.00/1.01  --qbf_pred_elim                         true
% 2.00/1.01  --qbf_split                             512
% 2.00/1.01  
% 2.00/1.01  ------ BMC1 Options
% 2.00/1.01  
% 2.00/1.01  --bmc1_incremental                      false
% 2.00/1.01  --bmc1_axioms                           reachable_all
% 2.00/1.01  --bmc1_min_bound                        0
% 2.00/1.01  --bmc1_max_bound                        -1
% 2.00/1.01  --bmc1_max_bound_default                -1
% 2.00/1.01  --bmc1_symbol_reachability              true
% 2.00/1.01  --bmc1_property_lemmas                  false
% 2.00/1.01  --bmc1_k_induction                      false
% 2.00/1.01  --bmc1_non_equiv_states                 false
% 2.00/1.01  --bmc1_deadlock                         false
% 2.00/1.01  --bmc1_ucm                              false
% 2.00/1.01  --bmc1_add_unsat_core                   none
% 2.00/1.01  --bmc1_unsat_core_children              false
% 2.00/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.00/1.01  --bmc1_out_stat                         full
% 2.00/1.01  --bmc1_ground_init                      false
% 2.00/1.01  --bmc1_pre_inst_next_state              false
% 2.00/1.01  --bmc1_pre_inst_state                   false
% 2.00/1.01  --bmc1_pre_inst_reach_state             false
% 2.00/1.01  --bmc1_out_unsat_core                   false
% 2.00/1.01  --bmc1_aig_witness_out                  false
% 2.00/1.01  --bmc1_verbose                          false
% 2.00/1.01  --bmc1_dump_clauses_tptp                false
% 2.00/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.00/1.01  --bmc1_dump_file                        -
% 2.00/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.00/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.00/1.01  --bmc1_ucm_extend_mode                  1
% 2.00/1.01  --bmc1_ucm_init_mode                    2
% 2.00/1.01  --bmc1_ucm_cone_mode                    none
% 2.00/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.00/1.01  --bmc1_ucm_relax_model                  4
% 2.00/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.00/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.00/1.01  --bmc1_ucm_layered_model                none
% 2.00/1.01  --bmc1_ucm_max_lemma_size               10
% 2.00/1.01  
% 2.00/1.01  ------ AIG Options
% 2.00/1.01  
% 2.00/1.01  --aig_mode                              false
% 2.00/1.01  
% 2.00/1.01  ------ Instantiation Options
% 2.00/1.01  
% 2.00/1.01  --instantiation_flag                    true
% 2.00/1.01  --inst_sos_flag                         false
% 2.00/1.01  --inst_sos_phase                        true
% 2.00/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.00/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.00/1.01  --inst_lit_sel_side                     num_symb
% 2.00/1.01  --inst_solver_per_active                1400
% 2.00/1.01  --inst_solver_calls_frac                1.
% 2.00/1.01  --inst_passive_queue_type               priority_queues
% 2.00/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.00/1.01  --inst_passive_queues_freq              [25;2]
% 2.00/1.01  --inst_dismatching                      true
% 2.00/1.01  --inst_eager_unprocessed_to_passive     true
% 2.00/1.01  --inst_prop_sim_given                   true
% 2.00/1.01  --inst_prop_sim_new                     false
% 2.00/1.01  --inst_subs_new                         false
% 2.00/1.01  --inst_eq_res_simp                      false
% 2.00/1.01  --inst_subs_given                       false
% 2.00/1.01  --inst_orphan_elimination               true
% 2.00/1.01  --inst_learning_loop_flag               true
% 2.00/1.01  --inst_learning_start                   3000
% 2.00/1.01  --inst_learning_factor                  2
% 2.00/1.01  --inst_start_prop_sim_after_learn       3
% 2.00/1.01  --inst_sel_renew                        solver
% 2.00/1.01  --inst_lit_activity_flag                true
% 2.00/1.01  --inst_restr_to_given                   false
% 2.00/1.01  --inst_activity_threshold               500
% 2.00/1.01  --inst_out_proof                        true
% 2.00/1.01  
% 2.00/1.01  ------ Resolution Options
% 2.00/1.01  
% 2.00/1.01  --resolution_flag                       true
% 2.00/1.01  --res_lit_sel                           adaptive
% 2.00/1.01  --res_lit_sel_side                      none
% 2.00/1.01  --res_ordering                          kbo
% 2.00/1.01  --res_to_prop_solver                    active
% 2.00/1.01  --res_prop_simpl_new                    false
% 2.00/1.01  --res_prop_simpl_given                  true
% 2.00/1.01  --res_passive_queue_type                priority_queues
% 2.00/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.00/1.01  --res_passive_queues_freq               [15;5]
% 2.00/1.01  --res_forward_subs                      full
% 2.00/1.01  --res_backward_subs                     full
% 2.00/1.01  --res_forward_subs_resolution           true
% 2.00/1.01  --res_backward_subs_resolution          true
% 2.00/1.01  --res_orphan_elimination                true
% 2.00/1.01  --res_time_limit                        2.
% 2.00/1.01  --res_out_proof                         true
% 2.00/1.01  
% 2.00/1.01  ------ Superposition Options
% 2.00/1.01  
% 2.00/1.01  --superposition_flag                    true
% 2.00/1.01  --sup_passive_queue_type                priority_queues
% 2.00/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.00/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.00/1.01  --demod_completeness_check              fast
% 2.00/1.01  --demod_use_ground                      true
% 2.00/1.01  --sup_to_prop_solver                    passive
% 2.00/1.01  --sup_prop_simpl_new                    true
% 2.00/1.01  --sup_prop_simpl_given                  true
% 2.00/1.01  --sup_fun_splitting                     false
% 2.00/1.01  --sup_smt_interval                      50000
% 2.00/1.01  
% 2.00/1.01  ------ Superposition Simplification Setup
% 2.00/1.01  
% 2.00/1.01  --sup_indices_passive                   []
% 2.00/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.00/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.01  --sup_full_bw                           [BwDemod]
% 2.00/1.01  --sup_immed_triv                        [TrivRules]
% 2.00/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.00/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.01  --sup_immed_bw_main                     []
% 2.00/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.00/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/1.01  
% 2.00/1.01  ------ Combination Options
% 2.00/1.01  
% 2.00/1.01  --comb_res_mult                         3
% 2.00/1.01  --comb_sup_mult                         2
% 2.00/1.01  --comb_inst_mult                        10
% 2.00/1.01  
% 2.00/1.01  ------ Debug Options
% 2.00/1.01  
% 2.00/1.01  --dbg_backtrace                         false
% 2.00/1.01  --dbg_dump_prop_clauses                 false
% 2.00/1.01  --dbg_dump_prop_clauses_file            -
% 2.00/1.01  --dbg_out_stat                          false
% 2.00/1.01  ------ Parsing...
% 2.00/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.00/1.01  
% 2.00/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 2.00/1.01  
% 2.00/1.01  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.00/1.01  
% 2.00/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.00/1.01  ------ Proving...
% 2.00/1.01  ------ Problem Properties 
% 2.00/1.01  
% 2.00/1.01  
% 2.00/1.01  clauses                                 28
% 2.00/1.01  conjectures                             6
% 2.00/1.01  EPR                                     1
% 2.00/1.01  Horn                                    23
% 2.00/1.01  unary                                   6
% 2.00/1.01  binary                                  6
% 2.00/1.01  lits                                    86
% 2.00/1.01  lits eq                                 3
% 2.00/1.01  fd_pure                                 0
% 2.00/1.01  fd_pseudo                               0
% 2.00/1.01  fd_cond                                 0
% 2.00/1.01  fd_pseudo_cond                          0
% 2.00/1.01  AC symbols                              0
% 2.00/1.01  
% 2.00/1.01  ------ Schedule dynamic 5 is on 
% 2.00/1.01  
% 2.00/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.00/1.01  
% 2.00/1.01  
% 2.00/1.01  ------ 
% 2.00/1.01  Current options:
% 2.00/1.01  ------ 
% 2.00/1.01  
% 2.00/1.01  ------ Input Options
% 2.00/1.01  
% 2.00/1.01  --out_options                           all
% 2.00/1.01  --tptp_safe_out                         true
% 2.00/1.01  --problem_path                          ""
% 2.00/1.01  --include_path                          ""
% 2.00/1.01  --clausifier                            res/vclausify_rel
% 2.00/1.01  --clausifier_options                    --mode clausify
% 2.00/1.01  --stdin                                 false
% 2.00/1.01  --stats_out                             all
% 2.00/1.01  
% 2.00/1.01  ------ General Options
% 2.00/1.01  
% 2.00/1.01  --fof                                   false
% 2.00/1.01  --time_out_real                         305.
% 2.00/1.01  --time_out_virtual                      -1.
% 2.00/1.01  --symbol_type_check                     false
% 2.00/1.01  --clausify_out                          false
% 2.00/1.01  --sig_cnt_out                           false
% 2.00/1.01  --trig_cnt_out                          false
% 2.00/1.01  --trig_cnt_out_tolerance                1.
% 2.00/1.01  --trig_cnt_out_sk_spl                   false
% 2.00/1.01  --abstr_cl_out                          false
% 2.00/1.01  
% 2.00/1.01  ------ Global Options
% 2.00/1.01  
% 2.00/1.01  --schedule                              default
% 2.00/1.01  --add_important_lit                     false
% 2.00/1.01  --prop_solver_per_cl                    1000
% 2.00/1.01  --min_unsat_core                        false
% 2.00/1.01  --soft_assumptions                      false
% 2.00/1.01  --soft_lemma_size                       3
% 2.00/1.01  --prop_impl_unit_size                   0
% 2.00/1.01  --prop_impl_unit                        []
% 2.00/1.01  --share_sel_clauses                     true
% 2.00/1.01  --reset_solvers                         false
% 2.00/1.01  --bc_imp_inh                            [conj_cone]
% 2.00/1.01  --conj_cone_tolerance                   3.
% 2.00/1.01  --extra_neg_conj                        none
% 2.00/1.01  --large_theory_mode                     true
% 2.00/1.01  --prolific_symb_bound                   200
% 2.00/1.01  --lt_threshold                          2000
% 2.00/1.01  --clause_weak_htbl                      true
% 2.00/1.01  --gc_record_bc_elim                     false
% 2.00/1.01  
% 2.00/1.01  ------ Preprocessing Options
% 2.00/1.01  
% 2.00/1.01  --preprocessing_flag                    true
% 2.00/1.01  --time_out_prep_mult                    0.1
% 2.00/1.01  --splitting_mode                        input
% 2.00/1.01  --splitting_grd                         true
% 2.00/1.01  --splitting_cvd                         false
% 2.00/1.01  --splitting_cvd_svl                     false
% 2.00/1.01  --splitting_nvd                         32
% 2.00/1.01  --sub_typing                            true
% 2.00/1.01  --prep_gs_sim                           true
% 2.00/1.01  --prep_unflatten                        true
% 2.00/1.01  --prep_res_sim                          true
% 2.00/1.01  --prep_upred                            true
% 2.00/1.01  --prep_sem_filter                       exhaustive
% 2.00/1.01  --prep_sem_filter_out                   false
% 2.00/1.01  --pred_elim                             true
% 2.00/1.01  --res_sim_input                         true
% 2.00/1.01  --eq_ax_congr_red                       true
% 2.00/1.01  --pure_diseq_elim                       true
% 2.00/1.01  --brand_transform                       false
% 2.00/1.01  --non_eq_to_eq                          false
% 2.00/1.01  --prep_def_merge                        true
% 2.00/1.01  --prep_def_merge_prop_impl              false
% 2.00/1.01  --prep_def_merge_mbd                    true
% 2.00/1.01  --prep_def_merge_tr_red                 false
% 2.00/1.01  --prep_def_merge_tr_cl                  false
% 2.00/1.01  --smt_preprocessing                     true
% 2.00/1.01  --smt_ac_axioms                         fast
% 2.00/1.01  --preprocessed_out                      false
% 2.00/1.01  --preprocessed_stats                    false
% 2.00/1.01  
% 2.00/1.01  ------ Abstraction refinement Options
% 2.00/1.01  
% 2.00/1.01  --abstr_ref                             []
% 2.00/1.01  --abstr_ref_prep                        false
% 2.00/1.01  --abstr_ref_until_sat                   false
% 2.00/1.01  --abstr_ref_sig_restrict                funpre
% 2.00/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.00/1.01  --abstr_ref_under                       []
% 2.00/1.01  
% 2.00/1.01  ------ SAT Options
% 2.00/1.01  
% 2.00/1.01  --sat_mode                              false
% 2.00/1.01  --sat_fm_restart_options                ""
% 2.00/1.01  --sat_gr_def                            false
% 2.00/1.01  --sat_epr_types                         true
% 2.00/1.01  --sat_non_cyclic_types                  false
% 2.00/1.01  --sat_finite_models                     false
% 2.00/1.01  --sat_fm_lemmas                         false
% 2.00/1.01  --sat_fm_prep                           false
% 2.00/1.01  --sat_fm_uc_incr                        true
% 2.00/1.01  --sat_out_model                         small
% 2.00/1.01  --sat_out_clauses                       false
% 2.00/1.01  
% 2.00/1.01  ------ QBF Options
% 2.00/1.01  
% 2.00/1.01  --qbf_mode                              false
% 2.00/1.01  --qbf_elim_univ                         false
% 2.00/1.01  --qbf_dom_inst                          none
% 2.00/1.01  --qbf_dom_pre_inst                      false
% 2.00/1.01  --qbf_sk_in                             false
% 2.00/1.01  --qbf_pred_elim                         true
% 2.00/1.01  --qbf_split                             512
% 2.00/1.01  
% 2.00/1.01  ------ BMC1 Options
% 2.00/1.01  
% 2.00/1.01  --bmc1_incremental                      false
% 2.00/1.01  --bmc1_axioms                           reachable_all
% 2.00/1.01  --bmc1_min_bound                        0
% 2.00/1.01  --bmc1_max_bound                        -1
% 2.00/1.01  --bmc1_max_bound_default                -1
% 2.00/1.01  --bmc1_symbol_reachability              true
% 2.00/1.01  --bmc1_property_lemmas                  false
% 2.00/1.01  --bmc1_k_induction                      false
% 2.00/1.01  --bmc1_non_equiv_states                 false
% 2.00/1.01  --bmc1_deadlock                         false
% 2.00/1.01  --bmc1_ucm                              false
% 2.00/1.01  --bmc1_add_unsat_core                   none
% 2.00/1.01  --bmc1_unsat_core_children              false
% 2.00/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.00/1.01  --bmc1_out_stat                         full
% 2.00/1.01  --bmc1_ground_init                      false
% 2.00/1.01  --bmc1_pre_inst_next_state              false
% 2.00/1.01  --bmc1_pre_inst_state                   false
% 2.00/1.01  --bmc1_pre_inst_reach_state             false
% 2.00/1.01  --bmc1_out_unsat_core                   false
% 2.00/1.01  --bmc1_aig_witness_out                  false
% 2.00/1.01  --bmc1_verbose                          false
% 2.00/1.01  --bmc1_dump_clauses_tptp                false
% 2.00/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.00/1.01  --bmc1_dump_file                        -
% 2.00/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.00/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.00/1.01  --bmc1_ucm_extend_mode                  1
% 2.00/1.01  --bmc1_ucm_init_mode                    2
% 2.00/1.01  --bmc1_ucm_cone_mode                    none
% 2.00/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.00/1.01  --bmc1_ucm_relax_model                  4
% 2.00/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.00/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.00/1.01  --bmc1_ucm_layered_model                none
% 2.00/1.01  --bmc1_ucm_max_lemma_size               10
% 2.00/1.01  
% 2.00/1.01  ------ AIG Options
% 2.00/1.01  
% 2.00/1.01  --aig_mode                              false
% 2.00/1.01  
% 2.00/1.01  ------ Instantiation Options
% 2.00/1.01  
% 2.00/1.01  --instantiation_flag                    true
% 2.00/1.01  --inst_sos_flag                         false
% 2.00/1.01  --inst_sos_phase                        true
% 2.00/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.00/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.00/1.01  --inst_lit_sel_side                     none
% 2.00/1.01  --inst_solver_per_active                1400
% 2.00/1.01  --inst_solver_calls_frac                1.
% 2.00/1.01  --inst_passive_queue_type               priority_queues
% 2.00/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.00/1.01  --inst_passive_queues_freq              [25;2]
% 2.00/1.01  --inst_dismatching                      true
% 2.00/1.01  --inst_eager_unprocessed_to_passive     true
% 2.00/1.01  --inst_prop_sim_given                   true
% 2.00/1.01  --inst_prop_sim_new                     false
% 2.00/1.01  --inst_subs_new                         false
% 2.00/1.01  --inst_eq_res_simp                      false
% 2.00/1.01  --inst_subs_given                       false
% 2.00/1.01  --inst_orphan_elimination               true
% 2.00/1.01  --inst_learning_loop_flag               true
% 2.00/1.01  --inst_learning_start                   3000
% 2.00/1.01  --inst_learning_factor                  2
% 2.00/1.01  --inst_start_prop_sim_after_learn       3
% 2.00/1.01  --inst_sel_renew                        solver
% 2.00/1.01  --inst_lit_activity_flag                true
% 2.00/1.01  --inst_restr_to_given                   false
% 2.00/1.01  --inst_activity_threshold               500
% 2.00/1.01  --inst_out_proof                        true
% 2.00/1.01  
% 2.00/1.01  ------ Resolution Options
% 2.00/1.01  
% 2.00/1.01  --resolution_flag                       false
% 2.00/1.01  --res_lit_sel                           adaptive
% 2.00/1.01  --res_lit_sel_side                      none
% 2.00/1.01  --res_ordering                          kbo
% 2.00/1.01  --res_to_prop_solver                    active
% 2.00/1.01  --res_prop_simpl_new                    false
% 2.00/1.01  --res_prop_simpl_given                  true
% 2.00/1.01  --res_passive_queue_type                priority_queues
% 2.00/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.00/1.01  --res_passive_queues_freq               [15;5]
% 2.00/1.01  --res_forward_subs                      full
% 2.00/1.01  --res_backward_subs                     full
% 2.00/1.01  --res_forward_subs_resolution           true
% 2.00/1.01  --res_backward_subs_resolution          true
% 2.00/1.01  --res_orphan_elimination                true
% 2.00/1.01  --res_time_limit                        2.
% 2.00/1.01  --res_out_proof                         true
% 2.00/1.01  
% 2.00/1.01  ------ Superposition Options
% 2.00/1.01  
% 2.00/1.01  --superposition_flag                    true
% 2.00/1.01  --sup_passive_queue_type                priority_queues
% 2.00/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.00/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.00/1.01  --demod_completeness_check              fast
% 2.00/1.01  --demod_use_ground                      true
% 2.00/1.01  --sup_to_prop_solver                    passive
% 2.00/1.01  --sup_prop_simpl_new                    true
% 2.00/1.01  --sup_prop_simpl_given                  true
% 2.00/1.01  --sup_fun_splitting                     false
% 2.00/1.01  --sup_smt_interval                      50000
% 2.00/1.01  
% 2.00/1.01  ------ Superposition Simplification Setup
% 2.00/1.01  
% 2.00/1.01  --sup_indices_passive                   []
% 2.00/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.00/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.01  --sup_full_bw                           [BwDemod]
% 2.00/1.01  --sup_immed_triv                        [TrivRules]
% 2.00/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.00/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.01  --sup_immed_bw_main                     []
% 2.00/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.00/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/1.01  
% 2.00/1.01  ------ Combination Options
% 2.00/1.01  
% 2.00/1.01  --comb_res_mult                         3
% 2.00/1.01  --comb_sup_mult                         2
% 2.00/1.01  --comb_inst_mult                        10
% 2.00/1.01  
% 2.00/1.01  ------ Debug Options
% 2.00/1.01  
% 2.00/1.01  --dbg_backtrace                         false
% 2.00/1.01  --dbg_dump_prop_clauses                 false
% 2.00/1.01  --dbg_dump_prop_clauses_file            -
% 2.00/1.01  --dbg_out_stat                          false
% 2.00/1.01  
% 2.00/1.01  
% 2.00/1.01  
% 2.00/1.01  
% 2.00/1.01  ------ Proving...
% 2.00/1.01  
% 2.00/1.01  
% 2.00/1.01  % SZS status Theorem for theBenchmark.p
% 2.00/1.01  
% 2.00/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.00/1.01  
% 2.00/1.01  fof(f7,axiom,(
% 2.00/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 2.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.01  
% 2.00/1.01  fof(f24,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.00/1.01    inference(ennf_transformation,[],[f7])).
% 2.00/1.01  
% 2.00/1.01  fof(f25,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.00/1.01    inference(flattening,[],[f24])).
% 2.00/1.01  
% 2.00/1.01  fof(f35,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.00/1.01    inference(nnf_transformation,[],[f25])).
% 2.00/1.01  
% 2.00/1.01  fof(f36,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.00/1.01    inference(rectify,[],[f35])).
% 2.00/1.01  
% 2.00/1.01  fof(f38,plain,(
% 2.00/1.01    ! [X4,X1,X0] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK1(X0,X1,X4),X1) & m1_connsp_2(sK1(X0,X1,X4),X0,X4) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.00/1.01    introduced(choice_axiom,[])).
% 2.00/1.01  
% 2.00/1.01  fof(f37,plain,(
% 2.00/1.01    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK0(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 2.00/1.01    introduced(choice_axiom,[])).
% 2.00/1.01  
% 2.00/1.01  fof(f39,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK0(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X4] : ((r1_tarski(sK1(X0,X1,X4),X1) & m1_connsp_2(sK1(X0,X1,X4),X0,X4) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.00/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 2.00/1.01  
% 2.00/1.01  fof(f60,plain,(
% 2.00/1.01    ( ! [X4,X0,X1] : (r1_tarski(sK1(X0,X1,X4),X1) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.00/1.01    inference(cnf_transformation,[],[f39])).
% 2.00/1.01  
% 2.00/1.01  fof(f12,conjecture,(
% 2.00/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.01  
% 2.00/1.01  fof(f13,negated_conjecture,(
% 2.00/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.00/1.01    inference(negated_conjecture,[],[f12])).
% 2.00/1.01  
% 2.00/1.01  fof(f33,plain,(
% 2.00/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.00/1.01    inference(ennf_transformation,[],[f13])).
% 2.00/1.01  
% 2.00/1.01  fof(f34,plain,(
% 2.00/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.00/1.01    inference(flattening,[],[f33])).
% 2.00/1.01  
% 2.00/1.01  fof(f43,plain,(
% 2.00/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.00/1.01    inference(nnf_transformation,[],[f34])).
% 2.00/1.01  
% 2.00/1.01  fof(f44,plain,(
% 2.00/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.00/1.01    inference(flattening,[],[f43])).
% 2.00/1.01  
% 2.00/1.01  fof(f50,plain,(
% 2.00/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7) | r1_tmap_1(X1,X0,X2,X4)) & sK7 = X4 & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 2.00/1.01    introduced(choice_axiom,[])).
% 2.00/1.01  
% 2.00/1.01  fof(f49,plain,(
% 2.00/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK6)) & sK6 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK6,u1_struct_0(X1)))) )),
% 2.00/1.01    introduced(choice_axiom,[])).
% 2.00/1.01  
% 2.00/1.01  fof(f48,plain,(
% 2.00/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK5))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK5,X1) & v1_tsep_1(sK5,X1) & ~v2_struct_0(sK5))) )),
% 2.00/1.01    introduced(choice_axiom,[])).
% 2.00/1.01  
% 2.00/1.01  fof(f47,plain,(
% 2.00/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5) | ~r1_tmap_1(X1,X0,sK4,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5) | r1_tmap_1(X1,X0,sK4,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 2.00/1.01    introduced(choice_axiom,[])).
% 2.00/1.01  
% 2.00/1.01  fof(f46,plain,(
% 2.00/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5) | ~r1_tmap_1(sK3,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5) | r1_tmap_1(sK3,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK3))) & m1_pre_topc(X3,sK3) & v1_tsep_1(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 2.00/1.01    introduced(choice_axiom,[])).
% 2.00/1.01  
% 2.00/1.01  fof(f45,plain,(
% 2.00/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5) | ~r1_tmap_1(X1,sK2,X2,X4)) & (r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5) | r1_tmap_1(X1,sK2,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.00/1.01    introduced(choice_axiom,[])).
% 2.00/1.01  
% 2.00/1.01  fof(f51,plain,(
% 2.00/1.01    ((((((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~r1_tmap_1(sK3,sK2,sK4,sK6)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | r1_tmap_1(sK3,sK2,sK4,sK6)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK5))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_pre_topc(sK5,sK3) & v1_tsep_1(sK5,sK3) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.00/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f44,f50,f49,f48,f47,f46,f45])).
% 2.00/1.01  
% 2.00/1.01  fof(f75,plain,(
% 2.00/1.01    v2_pre_topc(sK3)),
% 2.00/1.01    inference(cnf_transformation,[],[f51])).
% 2.00/1.01  
% 2.00/1.01  fof(f74,plain,(
% 2.00/1.01    ~v2_struct_0(sK3)),
% 2.00/1.01    inference(cnf_transformation,[],[f51])).
% 2.00/1.01  
% 2.00/1.01  fof(f76,plain,(
% 2.00/1.01    l1_pre_topc(sK3)),
% 2.00/1.01    inference(cnf_transformation,[],[f51])).
% 2.00/1.01  
% 2.00/1.01  fof(f1,axiom,(
% 2.00/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.01  
% 2.00/1.01  fof(f14,plain,(
% 2.00/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.00/1.01    inference(ennf_transformation,[],[f1])).
% 2.00/1.01  
% 2.00/1.01  fof(f15,plain,(
% 2.00/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.00/1.01    inference(flattening,[],[f14])).
% 2.00/1.01  
% 2.00/1.01  fof(f52,plain,(
% 2.00/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.00/1.01    inference(cnf_transformation,[],[f15])).
% 2.00/1.01  
% 2.00/1.01  fof(f2,axiom,(
% 2.00/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.01  
% 2.00/1.01  fof(f16,plain,(
% 2.00/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.00/1.01    inference(ennf_transformation,[],[f2])).
% 2.00/1.01  
% 2.00/1.01  fof(f53,plain,(
% 2.00/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.00/1.01    inference(cnf_transformation,[],[f16])).
% 2.00/1.01  
% 2.00/1.01  fof(f4,axiom,(
% 2.00/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.01  
% 2.00/1.01  fof(f18,plain,(
% 2.00/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.00/1.01    inference(ennf_transformation,[],[f4])).
% 2.00/1.01  
% 2.00/1.01  fof(f19,plain,(
% 2.00/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.00/1.01    inference(flattening,[],[f18])).
% 2.00/1.01  
% 2.00/1.01  fof(f55,plain,(
% 2.00/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.00/1.01    inference(cnf_transformation,[],[f19])).
% 2.00/1.01  
% 2.00/1.01  fof(f3,axiom,(
% 2.00/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.01  
% 2.00/1.01  fof(f17,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.00/1.01    inference(ennf_transformation,[],[f3])).
% 2.00/1.01  
% 2.00/1.01  fof(f54,plain,(
% 2.00/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.00/1.01    inference(cnf_transformation,[],[f17])).
% 2.00/1.01  
% 2.00/1.01  fof(f82,plain,(
% 2.00/1.01    m1_pre_topc(sK5,sK3)),
% 2.00/1.01    inference(cnf_transformation,[],[f51])).
% 2.00/1.01  
% 2.00/1.01  fof(f80,plain,(
% 2.00/1.01    ~v2_struct_0(sK5)),
% 2.00/1.01    inference(cnf_transformation,[],[f51])).
% 2.00/1.01  
% 2.00/1.01  fof(f8,axiom,(
% 2.00/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.01  
% 2.00/1.01  fof(f26,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.00/1.01    inference(ennf_transformation,[],[f8])).
% 2.00/1.01  
% 2.00/1.01  fof(f27,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.00/1.01    inference(flattening,[],[f26])).
% 2.00/1.01  
% 2.00/1.01  fof(f40,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.00/1.01    inference(nnf_transformation,[],[f27])).
% 2.00/1.01  
% 2.00/1.01  fof(f41,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.00/1.01    inference(flattening,[],[f40])).
% 2.00/1.01  
% 2.00/1.01  fof(f64,plain,(
% 2.00/1.01    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.00/1.01    inference(cnf_transformation,[],[f41])).
% 2.00/1.01  
% 2.00/1.01  fof(f90,plain,(
% 2.00/1.01    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.00/1.01    inference(equality_resolution,[],[f64])).
% 2.00/1.01  
% 2.00/1.01  fof(f9,axiom,(
% 2.00/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.01  
% 2.00/1.01  fof(f28,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.00/1.01    inference(ennf_transformation,[],[f9])).
% 2.00/1.01  
% 2.00/1.01  fof(f67,plain,(
% 2.00/1.01    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.00/1.01    inference(cnf_transformation,[],[f28])).
% 2.00/1.01  
% 2.00/1.01  fof(f81,plain,(
% 2.00/1.01    v1_tsep_1(sK5,sK3)),
% 2.00/1.01    inference(cnf_transformation,[],[f51])).
% 2.00/1.01  
% 2.00/1.01  fof(f5,axiom,(
% 2.00/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.01  
% 2.00/1.01  fof(f20,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.00/1.01    inference(ennf_transformation,[],[f5])).
% 2.00/1.01  
% 2.00/1.01  fof(f21,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.00/1.01    inference(flattening,[],[f20])).
% 2.00/1.01  
% 2.00/1.01  fof(f56,plain,(
% 2.00/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.00/1.01    inference(cnf_transformation,[],[f21])).
% 2.00/1.01  
% 2.00/1.01  fof(f59,plain,(
% 2.00/1.01    ( ! [X4,X0,X1] : (m1_connsp_2(sK1(X0,X1,X4),X0,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.00/1.01    inference(cnf_transformation,[],[f39])).
% 2.00/1.01  
% 2.00/1.01  fof(f11,axiom,(
% 2.00/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.01  
% 2.00/1.01  fof(f31,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.00/1.01    inference(ennf_transformation,[],[f11])).
% 2.00/1.01  
% 2.00/1.01  fof(f32,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.00/1.01    inference(flattening,[],[f31])).
% 2.00/1.01  
% 2.00/1.01  fof(f42,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.00/1.01    inference(nnf_transformation,[],[f32])).
% 2.00/1.01  
% 2.00/1.01  fof(f70,plain,(
% 2.00/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.00/1.01    inference(cnf_transformation,[],[f42])).
% 2.00/1.01  
% 2.00/1.01  fof(f92,plain,(
% 2.00/1.01    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.00/1.01    inference(equality_resolution,[],[f70])).
% 2.00/1.01  
% 2.00/1.01  fof(f78,plain,(
% 2.00/1.01    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 2.00/1.01    inference(cnf_transformation,[],[f51])).
% 2.00/1.01  
% 2.00/1.01  fof(f77,plain,(
% 2.00/1.01    v1_funct_1(sK4)),
% 2.00/1.01    inference(cnf_transformation,[],[f51])).
% 2.00/1.01  
% 2.00/1.01  fof(f6,axiom,(
% 2.00/1.01    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.01  
% 2.00/1.01  fof(f22,plain,(
% 2.00/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.00/1.01    inference(ennf_transformation,[],[f6])).
% 2.00/1.01  
% 2.00/1.01  fof(f23,plain,(
% 2.00/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.00/1.01    inference(flattening,[],[f22])).
% 2.00/1.01  
% 2.00/1.01  fof(f57,plain,(
% 2.00/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.00/1.01    inference(cnf_transformation,[],[f23])).
% 2.00/1.01  
% 2.00/1.01  fof(f72,plain,(
% 2.00/1.01    v2_pre_topc(sK2)),
% 2.00/1.01    inference(cnf_transformation,[],[f51])).
% 2.00/1.01  
% 2.00/1.01  fof(f71,plain,(
% 2.00/1.01    ~v2_struct_0(sK2)),
% 2.00/1.01    inference(cnf_transformation,[],[f51])).
% 2.00/1.01  
% 2.00/1.01  fof(f73,plain,(
% 2.00/1.01    l1_pre_topc(sK2)),
% 2.00/1.01    inference(cnf_transformation,[],[f51])).
% 2.00/1.01  
% 2.00/1.01  fof(f79,plain,(
% 2.00/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 2.00/1.01    inference(cnf_transformation,[],[f51])).
% 2.00/1.01  
% 2.00/1.01  fof(f69,plain,(
% 2.00/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.00/1.01    inference(cnf_transformation,[],[f42])).
% 2.00/1.01  
% 2.00/1.01  fof(f93,plain,(
% 2.00/1.01    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.00/1.01    inference(equality_resolution,[],[f69])).
% 2.00/1.01  
% 2.00/1.01  fof(f10,axiom,(
% 2.00/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.01  
% 2.00/1.01  fof(f29,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.00/1.01    inference(ennf_transformation,[],[f10])).
% 2.00/1.01  
% 2.00/1.01  fof(f30,plain,(
% 2.00/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.00/1.01    inference(flattening,[],[f29])).
% 2.00/1.01  
% 2.00/1.01  fof(f68,plain,(
% 2.00/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.00/1.01    inference(cnf_transformation,[],[f30])).
% 2.00/1.01  
% 2.00/1.01  fof(f91,plain,(
% 2.00/1.01    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.00/1.01    inference(equality_resolution,[],[f68])).
% 2.00/1.01  
% 2.00/1.01  fof(f87,plain,(
% 2.00/1.01    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~r1_tmap_1(sK3,sK2,sK4,sK6)),
% 2.00/1.01    inference(cnf_transformation,[],[f51])).
% 2.00/1.01  
% 2.00/1.01  fof(f85,plain,(
% 2.00/1.01    sK6 = sK7),
% 2.00/1.01    inference(cnf_transformation,[],[f51])).
% 2.00/1.01  
% 2.00/1.01  fof(f86,plain,(
% 2.00/1.01    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | r1_tmap_1(sK3,sK2,sK4,sK6)),
% 2.00/1.01    inference(cnf_transformation,[],[f51])).
% 2.00/1.01  
% 2.00/1.01  fof(f84,plain,(
% 2.00/1.01    m1_subset_1(sK7,u1_struct_0(sK5))),
% 2.00/1.01    inference(cnf_transformation,[],[f51])).
% 2.00/1.01  
% 2.00/1.01  cnf(c_9,plain,
% 2.00/1.01      ( r1_tarski(sK1(X0,X1,X2),X1)
% 2.00/1.01      | ~ v3_pre_topc(X1,X0)
% 2.00/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.00/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.00/1.01      | ~ r2_hidden(X2,X1)
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | ~ l1_pre_topc(X0) ),
% 2.00/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_31,negated_conjecture,
% 2.00/1.01      ( v2_pre_topc(sK3) ),
% 2.00/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_1788,plain,
% 2.00/1.01      ( r1_tarski(sK1(X0,X1,X2),X1)
% 2.00/1.01      | ~ v3_pre_topc(X1,X0)
% 2.00/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.00/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.00/1.01      | ~ r2_hidden(X2,X1)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | ~ l1_pre_topc(X0)
% 2.00/1.01      | sK3 != X0 ),
% 2.00/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_31]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_1789,plain,
% 2.00/1.01      ( r1_tarski(sK1(sK3,X0,X1),X0)
% 2.00/1.01      | ~ v3_pre_topc(X0,sK3)
% 2.00/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.00/1.01      | ~ r2_hidden(X1,X0)
% 2.00/1.01      | v2_struct_0(sK3)
% 2.00/1.01      | ~ l1_pre_topc(sK3) ),
% 2.00/1.01      inference(unflattening,[status(thm)],[c_1788]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_32,negated_conjecture,
% 2.00/1.01      ( ~ v2_struct_0(sK3) ),
% 2.00/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_30,negated_conjecture,
% 2.00/1.01      ( l1_pre_topc(sK3) ),
% 2.00/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_1793,plain,
% 2.00/1.01      ( r1_tarski(sK1(sK3,X0,X1),X0)
% 2.00/1.01      | ~ v3_pre_topc(X0,sK3)
% 2.00/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.00/1.01      | ~ r2_hidden(X1,X0) ),
% 2.00/1.01      inference(global_propositional_subsumption,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_1789,c_32,c_30]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_0,plain,
% 2.00/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.00/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_1,plain,
% 2.00/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.00/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_3,plain,
% 2.00/1.01      ( v2_struct_0(X0)
% 2.00/1.01      | ~ l1_struct_0(X0)
% 2.00/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.00/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_462,plain,
% 2.00/1.01      ( v2_struct_0(X0)
% 2.00/1.01      | ~ l1_pre_topc(X0)
% 2.00/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.00/1.01      inference(resolution,[status(thm)],[c_1,c_3]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_2,plain,
% 2.00/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.00/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_24,negated_conjecture,
% 2.00/1.01      ( m1_pre_topc(sK5,sK3) ),
% 2.00/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_917,plain,
% 2.00/1.01      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK3 != X0 | sK5 != X1 ),
% 2.00/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_24]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_918,plain,
% 2.00/1.01      ( ~ l1_pre_topc(sK3) | l1_pre_topc(sK5) ),
% 2.00/1.01      inference(unflattening,[status(thm)],[c_917]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_920,plain,
% 2.00/1.01      ( l1_pre_topc(sK5) ),
% 2.00/1.01      inference(global_propositional_subsumption,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_918,c_30]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_2172,plain,
% 2.00/1.01      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK5 != X0 ),
% 2.00/1.01      inference(resolution_lifted,[status(thm)],[c_462,c_920]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_2173,plain,
% 2.00/1.01      ( v2_struct_0(sK5) | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 2.00/1.01      inference(unflattening,[status(thm)],[c_2172]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_26,negated_conjecture,
% 2.00/1.01      ( ~ v2_struct_0(sK5) ),
% 2.00/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_2175,plain,
% 2.00/1.01      ( ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 2.00/1.01      inference(global_propositional_subsumption,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_2173,c_26]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_2213,plain,
% 2.00/1.01      ( ~ m1_subset_1(X0,X1)
% 2.00/1.01      | r2_hidden(X0,X1)
% 2.00/1.01      | u1_struct_0(sK5) != X1 ),
% 2.00/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_2175]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_2214,plain,
% 2.00/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.00/1.01      | r2_hidden(X0,u1_struct_0(sK5)) ),
% 2.00/1.01      inference(unflattening,[status(thm)],[c_2213]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_3178,plain,
% 2.00/1.01      ( r1_tarski(sK1(sK3,X0,X1),X0)
% 2.00/1.01      | ~ v3_pre_topc(X0,sK3)
% 2.00/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.00/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 2.00/1.01      | X2 != X1
% 2.00/1.01      | u1_struct_0(sK5) != X0 ),
% 2.00/1.01      inference(resolution_lifted,[status(thm)],[c_1793,c_2214]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_3179,plain,
% 2.00/1.01      ( r1_tarski(sK1(sK3,u1_struct_0(sK5),X0),u1_struct_0(sK5))
% 2.00/1.01      | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
% 2.00/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.00/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.00/1.01      inference(unflattening,[status(thm)],[c_3178]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_14,plain,
% 2.00/1.01      ( ~ v1_tsep_1(X0,X1)
% 2.00/1.01      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.00/1.01      | ~ m1_pre_topc(X0,X1)
% 2.00/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | ~ l1_pre_topc(X1) ),
% 2.00/1.01      inference(cnf_transformation,[],[f90]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_15,plain,
% 2.00/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.00/1.01      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.01      | ~ l1_pre_topc(X1) ),
% 2.00/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_198,plain,
% 2.00/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.00/1.01      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.00/1.01      | ~ v1_tsep_1(X0,X1)
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | ~ l1_pre_topc(X1) ),
% 2.00/1.01      inference(global_propositional_subsumption,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_14,c_15]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_199,plain,
% 2.00/1.01      ( ~ v1_tsep_1(X0,X1)
% 2.00/1.01      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.00/1.01      | ~ m1_pre_topc(X0,X1)
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | ~ l1_pre_topc(X1) ),
% 2.00/1.01      inference(renaming,[status(thm)],[c_198]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_25,negated_conjecture,
% 2.00/1.01      ( v1_tsep_1(sK5,sK3) ),
% 2.00/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_503,plain,
% 2.00/1.01      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.00/1.01      | ~ m1_pre_topc(X0,X1)
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | sK3 != X1
% 2.00/1.01      | sK5 != X0 ),
% 2.00/1.01      inference(resolution_lifted,[status(thm)],[c_199,c_25]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_504,plain,
% 2.00/1.01      ( v3_pre_topc(u1_struct_0(sK5),sK3)
% 2.00/1.01      | ~ m1_pre_topc(sK5,sK3)
% 2.00/1.01      | ~ v2_pre_topc(sK3)
% 2.00/1.01      | ~ l1_pre_topc(sK3) ),
% 2.00/1.01      inference(unflattening,[status(thm)],[c_503]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_888,plain,
% 2.00/1.01      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | sK3 != X1
% 2.00/1.01      | sK5 != X0 ),
% 2.00/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_889,plain,
% 2.00/1.01      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.00/1.01      | ~ l1_pre_topc(sK3) ),
% 2.00/1.01      inference(unflattening,[status(thm)],[c_888]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_4,plain,
% 2.00/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.00/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.00/1.01      | m1_subset_1(X2,u1_struct_0(X1))
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | ~ l1_pre_topc(X1) ),
% 2.00/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_899,plain,
% 2.00/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.00/1.01      | m1_subset_1(X0,u1_struct_0(X2))
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | v2_struct_0(X2)
% 2.00/1.01      | ~ l1_pre_topc(X2)
% 2.00/1.01      | sK3 != X2
% 2.00/1.01      | sK5 != X1 ),
% 2.00/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_900,plain,
% 2.00/1.01      ( m1_subset_1(X0,u1_struct_0(sK3))
% 2.00/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.00/1.01      | v2_struct_0(sK3)
% 2.00/1.01      | v2_struct_0(sK5)
% 2.00/1.01      | ~ l1_pre_topc(sK3) ),
% 2.00/1.01      inference(unflattening,[status(thm)],[c_899]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_904,plain,
% 2.00/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.00/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.00/1.01      inference(global_propositional_subsumption,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_900,c_32,c_30,c_26]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_905,plain,
% 2.00/1.01      ( m1_subset_1(X0,u1_struct_0(sK3))
% 2.00/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 2.00/1.01      inference(renaming,[status(thm)],[c_904]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_3183,plain,
% 2.00/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.00/1.01      | r1_tarski(sK1(sK3,u1_struct_0(sK5),X0),u1_struct_0(sK5)) ),
% 2.00/1.01      inference(global_propositional_subsumption,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_3179,c_32,c_31,c_30,c_26,c_24,c_504,c_889,c_900]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_3184,plain,
% 2.00/1.01      ( r1_tarski(sK1(sK3,u1_struct_0(sK5),X0),u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 2.00/1.01      inference(renaming,[status(thm)],[c_3183]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_10,plain,
% 2.00/1.01      ( m1_connsp_2(sK1(X0,X1,X2),X0,X2)
% 2.00/1.01      | ~ v3_pre_topc(X1,X0)
% 2.00/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.00/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.00/1.01      | ~ r2_hidden(X2,X1)
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | ~ l1_pre_topc(X0) ),
% 2.00/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_17,plain,
% 2.00/1.01      ( r1_tmap_1(X0,X1,X2,X3)
% 2.00/1.01      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.00/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.00/1.01      | ~ m1_connsp_2(X5,X0,X3)
% 2.00/1.01      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.00/1.01      | ~ m1_pre_topc(X4,X0)
% 2.00/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.00/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.00/1.01      | ~ v1_funct_1(X2)
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | v2_struct_0(X4)
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | ~ l1_pre_topc(X0) ),
% 2.00/1.01      inference(cnf_transformation,[],[f92]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_28,negated_conjecture,
% 2.00/1.01      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 2.00/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_674,plain,
% 2.00/1.01      ( r1_tmap_1(X0,X1,X2,X3)
% 2.00/1.01      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.00/1.01      | ~ m1_connsp_2(X5,X0,X3)
% 2.00/1.01      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.00/1.01      | ~ m1_pre_topc(X4,X0)
% 2.00/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.00/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.00/1.01      | ~ v1_funct_1(X2)
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | v2_struct_0(X4)
% 2.00/1.01      | ~ l1_pre_topc(X0)
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.00/1.01      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.00/1.01      | sK4 != X2 ),
% 2.00/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_675,plain,
% 2.00/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.00/1.01      | r1_tmap_1(X2,X1,sK4,X3)
% 2.00/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.00/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.00/1.01      | ~ m1_pre_topc(X0,X2)
% 2.00/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.00/1.01      | ~ v1_funct_1(sK4)
% 2.00/1.01      | ~ v2_pre_topc(X2)
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | v2_struct_0(X2)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | ~ l1_pre_topc(X2)
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.00/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(unflattening,[status(thm)],[c_674]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_29,negated_conjecture,
% 2.00/1.01      ( v1_funct_1(sK4) ),
% 2.00/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_679,plain,
% 2.00/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.00/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.00/1.01      | ~ m1_pre_topc(X0,X2)
% 2.00/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.00/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.00/1.01      | r1_tmap_1(X2,X1,sK4,X3)
% 2.00/1.01      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.00/1.01      | ~ v2_pre_topc(X2)
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | v2_struct_0(X2)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | ~ l1_pre_topc(X2)
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.00/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(global_propositional_subsumption,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_675,c_29]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_680,plain,
% 2.00/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.00/1.01      | r1_tmap_1(X2,X1,sK4,X3)
% 2.00/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.00/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.00/1.01      | ~ m1_pre_topc(X0,X2)
% 2.00/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | ~ v2_pre_topc(X2)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | v2_struct_0(X2)
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | ~ l1_pre_topc(X2)
% 2.00/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.00/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(renaming,[status(thm)],[c_679]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_5,plain,
% 2.00/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 2.00/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | ~ l1_pre_topc(X1) ),
% 2.00/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_721,plain,
% 2.00/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.00/1.01      | r1_tmap_1(X2,X1,sK4,X3)
% 2.00/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.00/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.00/1.01      | ~ m1_pre_topc(X0,X2)
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | ~ v2_pre_topc(X2)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | v2_struct_0(X2)
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | ~ l1_pre_topc(X2)
% 2.00/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.00/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(forward_subsumption_resolution,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_680,c_4,c_5]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_928,plain,
% 2.00/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.00/1.01      | r1_tmap_1(X2,X1,sK4,X3)
% 2.00/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.00/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.00/1.01      | ~ v2_pre_topc(X2)
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | v2_struct_0(X2)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | ~ l1_pre_topc(X2)
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.00/1.01      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.00/1.01      | sK3 != X2
% 2.00/1.01      | sK5 != X0 ),
% 2.00/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_721]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_929,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.00/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.00/1.01      | ~ m1_connsp_2(X2,sK3,X1)
% 2.00/1.01      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | ~ v2_pre_topc(sK3)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | v2_struct_0(sK3)
% 2.00/1.01      | v2_struct_0(sK5)
% 2.00/1.01      | ~ l1_pre_topc(X0)
% 2.00/1.01      | ~ l1_pre_topc(sK3)
% 2.00/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.00/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.00/1.01      inference(unflattening,[status(thm)],[c_928]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_933,plain,
% 2.00/1.01      ( ~ l1_pre_topc(X0)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | r1_tmap_1(sK3,X0,sK4,X1)
% 2.00/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.00/1.01      | ~ m1_connsp_2(X2,sK3,X1)
% 2.00/1.01      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.00/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.00/1.01      inference(global_propositional_subsumption,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_929,c_32,c_31,c_30,c_26]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_934,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.00/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.00/1.01      | ~ m1_connsp_2(X2,sK3,X1)
% 2.00/1.01      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | ~ l1_pre_topc(X0)
% 2.00/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.00/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.00/1.01      inference(renaming,[status(thm)],[c_933]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_1168,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.00/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.00/1.01      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.00/1.01      | ~ v3_pre_topc(X3,X4)
% 2.00/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
% 2.00/1.01      | ~ m1_subset_1(X5,u1_struct_0(X4))
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.00/1.01      | ~ r2_hidden(X5,X3)
% 2.00/1.01      | ~ v2_pre_topc(X4)
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | v2_struct_0(X4)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | ~ l1_pre_topc(X4)
% 2.00/1.01      | ~ l1_pre_topc(X0)
% 2.00/1.01      | X1 != X5
% 2.00/1.01      | sK1(X4,X3,X5) != X2
% 2.00/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.00/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.00/1.01      | sK3 != X4 ),
% 2.00/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_934]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_1169,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.00/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.00/1.01      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 2.00/1.01      | ~ v3_pre_topc(X2,sK3)
% 2.00/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.00/1.01      | ~ r2_hidden(X1,X2)
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | ~ v2_pre_topc(sK3)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | v2_struct_0(sK3)
% 2.00/1.01      | ~ l1_pre_topc(X0)
% 2.00/1.01      | ~ l1_pre_topc(sK3)
% 2.00/1.01      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(unflattening,[status(thm)],[c_1168]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_1173,plain,
% 2.00/1.01      ( ~ l1_pre_topc(X0)
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | ~ r2_hidden(X1,X2)
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.00/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.00/1.01      | ~ v3_pre_topc(X2,sK3)
% 2.00/1.01      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 2.00/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.00/1.01      | r1_tmap_1(sK3,X0,sK4,X1)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(global_propositional_subsumption,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_1169,c_32,c_31,c_30]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_1174,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.00/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.00/1.01      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 2.00/1.01      | ~ v3_pre_topc(X2,sK3)
% 2.00/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.00/1.01      | ~ r2_hidden(X1,X2)
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | ~ l1_pre_topc(X0)
% 2.00/1.01      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(renaming,[status(thm)],[c_1173]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_1203,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.00/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.00/1.01      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 2.00/1.01      | ~ v3_pre_topc(X2,sK3)
% 2.00/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.00/1.01      | ~ r2_hidden(X1,X2)
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | ~ l1_pre_topc(X0)
% 2.00/1.01      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(forward_subsumption_resolution,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_1174,c_905]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_34,negated_conjecture,
% 2.00/1.01      ( v2_pre_topc(sK2) ),
% 2.00/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_1815,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.00/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.00/1.01      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 2.00/1.01      | ~ v3_pre_topc(X2,sK3)
% 2.00/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.00/1.01      | ~ r2_hidden(X1,X2)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | ~ l1_pre_topc(X0)
% 2.00/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.00/1.01      | sK2 != X0 ),
% 2.00/1.01      inference(resolution_lifted,[status(thm)],[c_1203,c_34]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_1816,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.00/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.00/1.01      | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
% 2.00/1.01      | ~ v3_pre_topc(X1,sK3)
% 2.00/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.00/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 2.00/1.01      | ~ r2_hidden(X0,X1)
% 2.00/1.01      | v2_struct_0(sK2)
% 2.00/1.01      | ~ l1_pre_topc(sK2)
% 2.00/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(unflattening,[status(thm)],[c_1815]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_35,negated_conjecture,
% 2.00/1.01      ( ~ v2_struct_0(sK2) ),
% 2.00/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_33,negated_conjecture,
% 2.00/1.01      ( l1_pre_topc(sK2) ),
% 2.00/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_27,negated_conjecture,
% 2.00/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 2.00/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_1820,plain,
% 2.00/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.00/1.01      | ~ v3_pre_topc(X1,sK3)
% 2.00/1.01      | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
% 2.00/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.00/1.01      | r1_tmap_1(sK3,sK2,sK4,X0)
% 2.00/1.01      | ~ r2_hidden(X0,X1)
% 2.00/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(global_propositional_subsumption,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_1816,c_35,c_33,c_27]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_1821,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.00/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.00/1.01      | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
% 2.00/1.01      | ~ v3_pre_topc(X1,sK3)
% 2.00/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.00/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.00/1.01      | ~ r2_hidden(X0,X1)
% 2.00/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(renaming,[status(thm)],[c_1820]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_2699,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.00/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.00/1.01      | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
% 2.00/1.01      | ~ v3_pre_topc(X1,sK3)
% 2.00/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.00/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 2.00/1.01      | X2 != X0
% 2.00/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.00/1.01      | u1_struct_0(sK5) != X1 ),
% 2.00/1.01      inference(resolution_lifted,[status(thm)],[c_1821,c_2214]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_2700,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.00/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.00/1.01      | ~ r1_tarski(sK1(sK3,u1_struct_0(sK5),X0),u1_struct_0(sK5))
% 2.00/1.01      | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
% 2.00/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.00/1.01      inference(unflattening,[status(thm)],[c_2699]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_2704,plain,
% 2.00/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.00/1.01      | r1_tmap_1(sK3,sK2,sK4,X0)
% 2.00/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.00/1.01      | ~ r1_tarski(sK1(sK3,u1_struct_0(sK5),X0),u1_struct_0(sK5)) ),
% 2.00/1.01      inference(global_propositional_subsumption,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_2700,c_31,c_30,c_24,c_504,c_889]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_2705,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.00/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.00/1.01      | ~ r1_tarski(sK1(sK3,u1_struct_0(sK5),X0),u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 2.00/1.01      inference(renaming,[status(thm)],[c_2704]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_3194,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.00/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.00/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 2.00/1.01      inference(backward_subsumption_resolution,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_3184,c_2705]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_5365,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,sK2,sK4,X0_56)
% 2.00/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_56)
% 2.00/1.01      | ~ m1_subset_1(X0_56,u1_struct_0(sK5)) ),
% 2.00/1.01      inference(subtyping,[status(esa)],[c_3194]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_6374,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.00/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.00/1.01      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 2.00/1.01      inference(instantiation,[status(thm)],[c_5365]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_6375,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
% 2.00/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top
% 2.00/1.01      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 2.00/1.01      inference(predicate_to_equality,[status(thm)],[c_6374]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_18,plain,
% 2.00/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.00/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.00/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.00/1.01      | ~ m1_connsp_2(X5,X0,X3)
% 2.00/1.01      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.00/1.01      | ~ m1_pre_topc(X4,X0)
% 2.00/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.00/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.00/1.01      | ~ v1_funct_1(X2)
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | v2_struct_0(X4)
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | ~ l1_pre_topc(X0) ),
% 2.00/1.01      inference(cnf_transformation,[],[f93]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_16,plain,
% 2.00/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.00/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.00/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.00/1.01      | ~ m1_pre_topc(X4,X0)
% 2.00/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.00/1.01      | ~ v1_funct_1(X2)
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | v2_struct_0(X4)
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | ~ l1_pre_topc(X0) ),
% 2.00/1.01      inference(cnf_transformation,[],[f91]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_190,plain,
% 2.00/1.01      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.00/1.01      | ~ m1_pre_topc(X4,X0)
% 2.00/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.00/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.00/1.01      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.00/1.01      | ~ v1_funct_1(X2)
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | v2_struct_0(X4)
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | ~ l1_pre_topc(X0) ),
% 2.00/1.01      inference(global_propositional_subsumption,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_18,c_16]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_191,plain,
% 2.00/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.00/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.00/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.00/1.01      | ~ m1_pre_topc(X4,X0)
% 2.00/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.00/1.01      | ~ v1_funct_1(X2)
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | v2_struct_0(X4)
% 2.00/1.01      | ~ l1_pre_topc(X0)
% 2.00/1.01      | ~ l1_pre_topc(X1) ),
% 2.00/1.01      inference(renaming,[status(thm)],[c_190]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_617,plain,
% 2.00/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.00/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.00/1.01      | ~ m1_pre_topc(X4,X0)
% 2.00/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.00/1.01      | ~ v1_funct_1(X2)
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | v2_struct_0(X4)
% 2.00/1.01      | ~ l1_pre_topc(X0)
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.00/1.01      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.00/1.01      | sK4 != X2 ),
% 2.00/1.01      inference(resolution_lifted,[status(thm)],[c_191,c_28]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_618,plain,
% 2.00/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.00/1.01      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.00/1.01      | ~ m1_pre_topc(X0,X2)
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.00/1.01      | ~ v1_funct_1(sK4)
% 2.00/1.01      | ~ v2_pre_topc(X2)
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | v2_struct_0(X2)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | ~ l1_pre_topc(X2)
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.00/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(unflattening,[status(thm)],[c_617]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_622,plain,
% 2.00/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.00/1.01      | ~ m1_pre_topc(X0,X2)
% 2.00/1.01      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.00/1.01      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.00/1.01      | ~ v2_pre_topc(X2)
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | v2_struct_0(X2)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | ~ l1_pre_topc(X2)
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.00/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(global_propositional_subsumption,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_618,c_29]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_623,plain,
% 2.00/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.00/1.01      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.00/1.01      | ~ m1_pre_topc(X0,X2)
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | ~ v2_pre_topc(X2)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | v2_struct_0(X2)
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | ~ l1_pre_topc(X2)
% 2.00/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.00/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(renaming,[status(thm)],[c_622]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_658,plain,
% 2.00/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.00/1.01      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.00/1.01      | ~ m1_pre_topc(X0,X2)
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | ~ v2_pre_topc(X2)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | v2_struct_0(X2)
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | ~ l1_pre_topc(X2)
% 2.00/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.00/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_623,c_4]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_973,plain,
% 2.00/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.00/1.01      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.00/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.00/1.01      | ~ v2_pre_topc(X2)
% 2.00/1.01      | ~ v2_pre_topc(X1)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | v2_struct_0(X2)
% 2.00/1.01      | v2_struct_0(X1)
% 2.00/1.01      | ~ l1_pre_topc(X2)
% 2.00/1.01      | ~ l1_pre_topc(X1)
% 2.00/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.00/1.01      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.00/1.01      | sK3 != X2
% 2.00/1.01      | sK5 != X0 ),
% 2.00/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_658]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_974,plain,
% 2.00/1.01      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.00/1.01      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | ~ v2_pre_topc(sK3)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | v2_struct_0(sK3)
% 2.00/1.01      | v2_struct_0(sK5)
% 2.00/1.01      | ~ l1_pre_topc(X0)
% 2.00/1.01      | ~ l1_pre_topc(sK3)
% 2.00/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.00/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.00/1.01      inference(unflattening,[status(thm)],[c_973]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_978,plain,
% 2.00/1.01      ( ~ l1_pre_topc(X0)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.00/1.01      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.00/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.00/1.01      inference(global_propositional_subsumption,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_974,c_32,c_31,c_30,c_26]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_979,plain,
% 2.00/1.01      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.00/1.01      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.00/1.01      | ~ v2_pre_topc(X0)
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | ~ l1_pre_topc(X0)
% 2.00/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.00/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.00/1.01      inference(renaming,[status(thm)],[c_978]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_1877,plain,
% 2.00/1.01      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.00/1.01      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.00/1.01      | v2_struct_0(X0)
% 2.00/1.01      | ~ l1_pre_topc(X0)
% 2.00/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.00/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.00/1.01      | sK2 != X0 ),
% 2.00/1.01      inference(resolution_lifted,[status(thm)],[c_979,c_34]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_1878,plain,
% 2.00/1.01      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.00/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.00/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.00/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 2.00/1.01      | v2_struct_0(sK2)
% 2.00/1.01      | ~ l1_pre_topc(sK2)
% 2.00/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(unflattening,[status(thm)],[c_1877]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_1882,plain,
% 2.00/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.00/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.00/1.01      | ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.00/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(global_propositional_subsumption,
% 2.00/1.01                [status(thm)],
% 2.00/1.01                [c_1878,c_35,c_33,c_27]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_1883,plain,
% 2.00/1.01      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.00/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.00/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.00/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.00/1.01      inference(renaming,[status(thm)],[c_1882]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_4345,plain,
% 2.00/1.01      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.00/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.00/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 2.00/1.01      inference(equality_resolution_simp,[status(thm)],[c_1883]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_5364,plain,
% 2.00/1.01      ( ~ r1_tmap_1(sK3,sK2,sK4,X0_56)
% 2.00/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_56)
% 2.00/1.01      | ~ m1_subset_1(X0_56,u1_struct_0(sK5)) ),
% 2.00/1.01      inference(subtyping,[status(esa)],[c_4345]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_6368,plain,
% 2.00/1.01      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.00/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.00/1.01      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 2.00/1.01      inference(instantiation,[status(thm)],[c_5364]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_6369,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
% 2.00/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top
% 2.00/1.01      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 2.00/1.01      inference(predicate_to_equality,[status(thm)],[c_6368]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_19,negated_conjecture,
% 2.00/1.01      ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
% 2.00/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 2.00/1.01      inference(cnf_transformation,[],[f87]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_5389,negated_conjecture,
% 2.00/1.01      ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
% 2.00/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 2.00/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_6077,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,sK2,sK4,sK6) != iProver_top
% 2.00/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
% 2.00/1.01      inference(predicate_to_equality,[status(thm)],[c_5389]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_21,negated_conjecture,
% 2.00/1.01      ( sK6 = sK7 ),
% 2.00/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_5387,negated_conjecture,
% 2.00/1.01      ( sK6 = sK7 ),
% 2.00/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_6138,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
% 2.00/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
% 2.00/1.01      inference(light_normalisation,[status(thm)],[c_6077,c_5387]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_20,negated_conjecture,
% 2.00/1.01      ( r1_tmap_1(sK3,sK2,sK4,sK6)
% 2.00/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 2.00/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_5388,negated_conjecture,
% 2.00/1.01      ( r1_tmap_1(sK3,sK2,sK4,sK6)
% 2.00/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 2.00/1.01      inference(subtyping,[status(esa)],[c_20]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_6078,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,sK2,sK4,sK6) = iProver_top
% 2.00/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
% 2.00/1.01      inference(predicate_to_equality,[status(thm)],[c_5388]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_6133,plain,
% 2.00/1.01      ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
% 2.00/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
% 2.00/1.01      inference(light_normalisation,[status(thm)],[c_6078,c_5387]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_22,negated_conjecture,
% 2.00/1.01      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 2.00/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(c_49,plain,
% 2.00/1.01      ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
% 2.00/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.00/1.01  
% 2.00/1.01  cnf(contradiction,plain,
% 2.00/1.01      ( $false ),
% 2.00/1.01      inference(minisat,[status(thm)],[c_6375,c_6369,c_6138,c_6133,c_49]) ).
% 2.00/1.01  
% 2.00/1.01  
% 2.00/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.00/1.01  
% 2.00/1.01  ------                               Statistics
% 2.00/1.01  
% 2.00/1.01  ------ General
% 2.00/1.01  
% 2.00/1.01  abstr_ref_over_cycles:                  0
% 2.00/1.01  abstr_ref_under_cycles:                 0
% 2.00/1.01  gc_basic_clause_elim:                   0
% 2.00/1.01  forced_gc_time:                         0
% 2.00/1.01  parsing_time:                           0.01
% 2.00/1.01  unif_index_cands_time:                  0.
% 2.00/1.01  unif_index_add_time:                    0.
% 2.00/1.01  orderings_time:                         0.
% 2.00/1.01  out_proof_time:                         0.013
% 2.00/1.01  total_time:                             0.203
% 2.00/1.01  num_of_symbols:                         62
% 2.00/1.01  num_of_terms:                           3652
% 2.00/1.01  
% 2.00/1.01  ------ Preprocessing
% 2.00/1.01  
% 2.00/1.01  num_of_splits:                          2
% 2.00/1.01  num_of_split_atoms:                     2
% 2.00/1.01  num_of_reused_defs:                     0
% 2.00/1.01  num_eq_ax_congr_red:                    22
% 2.00/1.01  num_of_sem_filtered_clauses:            1
% 2.00/1.01  num_of_subtypes:                        2
% 2.00/1.01  monotx_restored_types:                  0
% 2.00/1.01  sat_num_of_epr_types:                   0
% 2.00/1.01  sat_num_of_non_cyclic_types:            0
% 2.00/1.01  sat_guarded_non_collapsed_types:        0
% 2.00/1.01  num_pure_diseq_elim:                    0
% 2.00/1.01  simp_replaced_by:                       0
% 2.00/1.01  res_preprocessed:                       140
% 2.00/1.01  prep_upred:                             0
% 2.00/1.01  prep_unflattend:                        302
% 2.00/1.01  smt_new_axioms:                         0
% 2.00/1.01  pred_elim_cands:                        5
% 2.00/1.01  pred_elim:                              10
% 2.00/1.01  pred_elim_cl:                           9
% 2.00/1.01  pred_elim_cycles:                       22
% 2.00/1.01  merged_defs:                            8
% 2.00/1.01  merged_defs_ncl:                        0
% 2.00/1.01  bin_hyper_res:                          8
% 2.00/1.01  prep_cycles:                            4
% 2.00/1.01  pred_elim_time:                         0.122
% 2.00/1.01  splitting_time:                         0.
% 2.00/1.01  sem_filter_time:                        0.
% 2.00/1.01  monotx_time:                            0.
% 2.00/1.01  subtype_inf_time:                       0.
% 2.00/1.01  
% 2.00/1.01  ------ Problem properties
% 2.00/1.01  
% 2.00/1.01  clauses:                                28
% 2.00/1.01  conjectures:                            6
% 2.00/1.01  epr:                                    1
% 2.00/1.01  horn:                                   23
% 2.00/1.01  ground:                                 10
% 2.00/1.01  unary:                                  6
% 2.00/1.01  binary:                                 6
% 2.00/1.01  lits:                                   86
% 2.00/1.01  lits_eq:                                3
% 2.00/1.01  fd_pure:                                0
% 2.00/1.01  fd_pseudo:                              0
% 2.00/1.01  fd_cond:                                0
% 2.00/1.01  fd_pseudo_cond:                         0
% 2.00/1.01  ac_symbols:                             0
% 2.00/1.01  
% 2.00/1.01  ------ Propositional Solver
% 2.00/1.01  
% 2.00/1.01  prop_solver_calls:                      22
% 2.00/1.01  prop_fast_solver_calls:                 2438
% 2.00/1.01  smt_solver_calls:                       0
% 2.00/1.01  smt_fast_solver_calls:                  0
% 2.00/1.01  prop_num_of_clauses:                    683
% 2.00/1.01  prop_preprocess_simplified:             4516
% 2.00/1.01  prop_fo_subsumed:                       156
% 2.00/1.01  prop_solver_time:                       0.
% 2.00/1.01  smt_solver_time:                        0.
% 2.00/1.01  smt_fast_solver_time:                   0.
% 2.00/1.01  prop_fast_solver_time:                  0.
% 2.00/1.01  prop_unsat_core_time:                   0.
% 2.00/1.01  
% 2.00/1.01  ------ QBF
% 2.00/1.01  
% 2.00/1.01  qbf_q_res:                              0
% 2.00/1.01  qbf_num_tautologies:                    0
% 2.00/1.01  qbf_prep_cycles:                        0
% 2.00/1.01  
% 2.00/1.01  ------ BMC1
% 2.00/1.01  
% 2.00/1.01  bmc1_current_bound:                     -1
% 2.00/1.01  bmc1_last_solved_bound:                 -1
% 2.00/1.01  bmc1_unsat_core_size:                   -1
% 2.00/1.01  bmc1_unsat_core_parents_size:           -1
% 2.00/1.01  bmc1_merge_next_fun:                    0
% 2.00/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.00/1.01  
% 2.00/1.01  ------ Instantiation
% 2.00/1.01  
% 2.00/1.01  inst_num_of_clauses:                    47
% 2.00/1.01  inst_num_in_passive:                    9
% 2.00/1.01  inst_num_in_active:                     30
% 2.00/1.01  inst_num_in_unprocessed:                8
% 2.00/1.01  inst_num_of_loops:                      30
% 2.00/1.01  inst_num_of_learning_restarts:          0
% 2.00/1.01  inst_num_moves_active_passive:          0
% 2.00/1.01  inst_lit_activity:                      0
% 2.00/1.01  inst_lit_activity_moves:                0
% 2.00/1.01  inst_num_tautologies:                   0
% 2.00/1.01  inst_num_prop_implied:                  0
% 2.00/1.01  inst_num_existing_simplified:           0
% 2.00/1.01  inst_num_eq_res_simplified:             0
% 2.00/1.01  inst_num_child_elim:                    0
% 2.00/1.01  inst_num_of_dismatching_blockings:      0
% 2.00/1.01  inst_num_of_non_proper_insts:           8
% 2.00/1.01  inst_num_of_duplicates:                 0
% 2.00/1.01  inst_inst_num_from_inst_to_res:         0
% 2.00/1.01  inst_dismatching_checking_time:         0.
% 2.00/1.01  
% 2.00/1.01  ------ Resolution
% 2.00/1.01  
% 2.00/1.01  res_num_of_clauses:                     0
% 2.00/1.01  res_num_in_passive:                     0
% 2.00/1.01  res_num_in_active:                      0
% 2.00/1.01  res_num_of_loops:                       144
% 2.00/1.01  res_forward_subset_subsumed:            3
% 2.00/1.01  res_backward_subset_subsumed:           0
% 2.00/1.01  res_forward_subsumed:                   6
% 2.00/1.01  res_backward_subsumed:                  3
% 2.00/1.01  res_forward_subsumption_resolution:     7
% 2.00/1.01  res_backward_subsumption_resolution:    2
% 2.00/1.01  res_clause_to_clause_subsumption:       207
% 2.00/1.01  res_orphan_elimination:                 0
% 2.00/1.01  res_tautology_del:                      46
% 2.00/1.01  res_num_eq_res_simplified:              1
% 2.00/1.01  res_num_sel_changes:                    0
% 2.00/1.01  res_moves_from_active_to_pass:          0
% 2.00/1.01  
% 2.00/1.01  ------ Superposition
% 2.00/1.01  
% 2.00/1.01  sup_time_total:                         0.
% 2.00/1.01  sup_time_generating:                    0.
% 2.00/1.01  sup_time_sim_full:                      0.
% 2.00/1.01  sup_time_sim_immed:                     0.
% 2.00/1.01  
% 2.00/1.01  sup_num_of_clauses:                     28
% 2.00/1.01  sup_num_in_active:                      4
% 2.00/1.01  sup_num_in_passive:                     24
% 2.00/1.01  sup_num_of_loops:                       4
% 2.00/1.01  sup_fw_superposition:                   0
% 2.00/1.01  sup_bw_superposition:                   0
% 2.00/1.01  sup_immediate_simplified:               0
% 2.00/1.01  sup_given_eliminated:                   0
% 2.00/1.01  comparisons_done:                       0
% 2.00/1.01  comparisons_avoided:                    0
% 2.00/1.01  
% 2.00/1.01  ------ Simplifications
% 2.00/1.01  
% 2.00/1.01  
% 2.00/1.01  sim_fw_subset_subsumed:                 0
% 2.00/1.01  sim_bw_subset_subsumed:                 0
% 2.00/1.01  sim_fw_subsumed:                        0
% 2.00/1.01  sim_bw_subsumed:                        0
% 2.00/1.01  sim_fw_subsumption_res:                 0
% 2.00/1.01  sim_bw_subsumption_res:                 0
% 2.00/1.01  sim_tautology_del:                      0
% 2.00/1.01  sim_eq_tautology_del:                   0
% 2.00/1.01  sim_eq_res_simp:                        0
% 2.00/1.01  sim_fw_demodulated:                     0
% 2.00/1.01  sim_bw_demodulated:                     0
% 2.00/1.01  sim_light_normalised:                   3
% 2.00/1.01  sim_joinable_taut:                      0
% 2.00/1.01  sim_joinable_simp:                      0
% 2.00/1.01  sim_ac_normalised:                      0
% 2.00/1.01  sim_smt_subsumption:                    0
% 2.00/1.01  
%------------------------------------------------------------------------------
