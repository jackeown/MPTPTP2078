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
% DateTime   : Thu Dec  3 12:22:45 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  192 (1020 expanded)
%              Number of clauses        :  106 ( 173 expanded)
%              Number of leaves         :   21 ( 400 expanded)
%              Depth                    :   42
%              Number of atoms          : 1389 (16217 expanded)
%              Number of equality atoms :  126 (1186 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f41])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | ~ r1_tmap_1(X1,X0,X2,X4) )
          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | r1_tmap_1(X1,X0,X2,X4) )
          & X4 = X5
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5)
          | ~ r1_tmap_1(X1,X0,X2,X4) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5)
          | r1_tmap_1(X1,X0,X2,X4) )
        & sK5 = X4
        & m1_subset_1(sK5,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
              | ~ r1_tmap_1(X1,X0,X2,sK4) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | r1_tmap_1(X1,X0,X2,sK4) )
            & sK4 = X5
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
                ( ( ~ r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5)
                  | ~ r1_tmap_1(X1,X0,X2,X4) )
                & ( r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5)
                  | r1_tmap_1(X1,X0,X2,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_pre_topc(sK3,X1)
        & v1_tsep_1(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
                    ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5)
                      | ~ r1_tmap_1(X1,X0,sK2,X4) )
                    & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5)
                      | r1_tmap_1(X1,X0,sK2,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_pre_topc(X3,X1)
            & v1_tsep_1(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
                        ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(sK1,X0,X2,X4) )
                        & ( r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5)
                          | r1_tmap_1(sK1,X0,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(sK1)) )
                & m1_pre_topc(X3,sK1)
                & v1_tsep_1(X3,sK1)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
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
                          ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK0,X2,X4) )
                          & ( r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                            | r1_tmap_1(X1,sK0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
    & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | r1_tmap_1(sK1,sK0,sK2,sK4) )
    & sK4 = sK5
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_pre_topc(sK3,sK1)
    & v1_tsep_1(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f47,f53,f52,f51,f50,f49,f48])).

fof(f88,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f39])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f95,plain,(
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
    inference(equality_resolution,[],[f71])).

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
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f37])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,(
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
    inference(equality_resolution,[],[f70])).

fof(f80,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
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

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f77,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f78,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f74,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f73,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f75,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
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
    inference(equality_resolution,[],[f72])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

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

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f35])).

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

fof(f66,plain,(
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

fof(f92,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

cnf(c_19,negated_conjecture,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2083,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20,negated_conjecture,
    ( sK4 = sK5 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2106,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2083,c_20])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2084,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2111,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2084,c_20])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_48,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_17,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_15,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_180,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_15])).

cnf(c_181,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_180])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_816,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_181,c_27])).

cnf(c_817,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_816])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_821,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK2,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_817,c_28])).

cnf(c_822,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_821])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_857,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_822,c_8])).

cnf(c_1089,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK1 != X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_857])).

cnf(c_1090,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1089])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1094,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1090,c_31,c_30,c_29,c_25])).

cnf(c_1095,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1094])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1353,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1095,c_33])).

cnf(c_1354,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1353])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1358,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ r1_tmap_1(sK1,sK0,sK2,X0)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1354,c_34,c_32,c_26])).

cnf(c_1359,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_1358])).

cnf(c_1530,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1359])).

cnf(c_2224,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1530])).

cnf(c_2225,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2224])).

cnf(c_2286,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2111,c_48,c_2225])).

cnf(c_2292,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2106,c_48,c_2111,c_2225])).

cnf(c_5,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_436,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_5,c_7])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1078,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_1079,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1078])).

cnf(c_1081,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1079,c_29])).

cnf(c_1425,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_436,c_1081])).

cnf(c_1426,plain,
    ( v2_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1425])).

cnf(c_1428,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1426,c_25])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_16,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_618,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | X5 != X6
    | u1_struct_0(X4) != X7 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_619,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_659,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_619,c_8])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_10,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_13,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_188,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_14])).

cnf(c_189,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_188])).

cnf(c_24,negated_conjecture,
    ( v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_477,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_189,c_24])).

cnf(c_478,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_480,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_30,c_29,c_23])).

cnf(c_490,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK3) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_480])).

cnf(c_491,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_495,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | m1_connsp_2(u1_struct_0(sK3),sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_31,c_30,c_29])).

cnf(c_496,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_495])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_509,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_496,c_4])).

cnf(c_535,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X2)
    | X0 != X1
    | u1_struct_0(sK3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_509])).

cnf(c_536,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_681,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X5,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | X5 != X3
    | u1_struct_0(sK3) != X6
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_659,c_536])).

cnf(c_682,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_681])).

cnf(c_686,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_682,c_31,c_30,c_29])).

cnf(c_687,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_686])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_2,c_4])).

cnf(c_720,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_687,c_520])).

cnf(c_922,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_720])).

cnf(c_923,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_922])).

cnf(c_927,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_pre_topc(X0,sK1)
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_923,c_28])).

cnf(c_928,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_927])).

cnf(c_1128,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK1 != sK1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_928])).

cnf(c_1129,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1128])).

cnf(c_1049,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_1050,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1049])).

cnf(c_1133,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1129,c_29,c_25,c_1050])).

cnf(c_1134,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_1133])).

cnf(c_1323,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1134,c_33])).

cnf(c_1324,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1323])).

cnf(c_1328,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | r1_tmap_1(sK1,sK0,sK2,X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1324,c_34,c_32,c_26])).

cnf(c_1329,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_1328])).

cnf(c_1442,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1428,c_1329])).

cnf(c_1525,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(equality_resolution_simp,[status(thm)],[c_1442])).

cnf(c_2070,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1525])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2085,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2095,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2085,c_0])).

cnf(c_2174,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2070,c_2095])).

cnf(c_2599,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2292,c_2174])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2599,c_2286,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:22:10 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.66/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/0.99  
% 1.66/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.66/0.99  
% 1.66/0.99  ------  iProver source info
% 1.66/0.99  
% 1.66/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.66/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.66/0.99  git: non_committed_changes: false
% 1.66/0.99  git: last_make_outside_of_git: false
% 1.66/0.99  
% 1.66/0.99  ------ 
% 1.66/0.99  
% 1.66/0.99  ------ Input Options
% 1.66/0.99  
% 1.66/0.99  --out_options                           all
% 1.66/0.99  --tptp_safe_out                         true
% 1.66/0.99  --problem_path                          ""
% 1.66/0.99  --include_path                          ""
% 1.66/0.99  --clausifier                            res/vclausify_rel
% 1.66/0.99  --clausifier_options                    --mode clausify
% 1.66/0.99  --stdin                                 false
% 1.66/0.99  --stats_out                             all
% 1.66/0.99  
% 1.66/0.99  ------ General Options
% 1.66/0.99  
% 1.66/0.99  --fof                                   false
% 1.66/0.99  --time_out_real                         305.
% 1.66/0.99  --time_out_virtual                      -1.
% 1.66/0.99  --symbol_type_check                     false
% 1.66/0.99  --clausify_out                          false
% 1.66/0.99  --sig_cnt_out                           false
% 1.66/0.99  --trig_cnt_out                          false
% 1.66/0.99  --trig_cnt_out_tolerance                1.
% 1.66/0.99  --trig_cnt_out_sk_spl                   false
% 1.66/0.99  --abstr_cl_out                          false
% 1.66/0.99  
% 1.66/0.99  ------ Global Options
% 1.66/0.99  
% 1.66/0.99  --schedule                              default
% 1.66/0.99  --add_important_lit                     false
% 1.66/0.99  --prop_solver_per_cl                    1000
% 1.66/0.99  --min_unsat_core                        false
% 1.66/0.99  --soft_assumptions                      false
% 1.66/0.99  --soft_lemma_size                       3
% 1.66/0.99  --prop_impl_unit_size                   0
% 1.66/0.99  --prop_impl_unit                        []
% 1.66/0.99  --share_sel_clauses                     true
% 1.66/0.99  --reset_solvers                         false
% 1.66/0.99  --bc_imp_inh                            [conj_cone]
% 1.66/0.99  --conj_cone_tolerance                   3.
% 1.66/0.99  --extra_neg_conj                        none
% 1.66/0.99  --large_theory_mode                     true
% 1.66/0.99  --prolific_symb_bound                   200
% 1.66/0.99  --lt_threshold                          2000
% 1.66/0.99  --clause_weak_htbl                      true
% 1.66/0.99  --gc_record_bc_elim                     false
% 1.66/0.99  
% 1.66/0.99  ------ Preprocessing Options
% 1.66/0.99  
% 1.66/0.99  --preprocessing_flag                    true
% 1.66/0.99  --time_out_prep_mult                    0.1
% 1.66/0.99  --splitting_mode                        input
% 1.66/0.99  --splitting_grd                         true
% 1.66/0.99  --splitting_cvd                         false
% 1.66/0.99  --splitting_cvd_svl                     false
% 1.66/0.99  --splitting_nvd                         32
% 1.66/0.99  --sub_typing                            true
% 1.66/0.99  --prep_gs_sim                           true
% 1.66/0.99  --prep_unflatten                        true
% 1.66/0.99  --prep_res_sim                          true
% 1.66/0.99  --prep_upred                            true
% 1.66/0.99  --prep_sem_filter                       exhaustive
% 1.66/0.99  --prep_sem_filter_out                   false
% 1.66/0.99  --pred_elim                             true
% 1.66/0.99  --res_sim_input                         true
% 1.66/0.99  --eq_ax_congr_red                       true
% 1.66/0.99  --pure_diseq_elim                       true
% 1.66/0.99  --brand_transform                       false
% 1.66/0.99  --non_eq_to_eq                          false
% 1.66/0.99  --prep_def_merge                        true
% 1.66/0.99  --prep_def_merge_prop_impl              false
% 1.66/0.99  --prep_def_merge_mbd                    true
% 1.66/0.99  --prep_def_merge_tr_red                 false
% 1.66/0.99  --prep_def_merge_tr_cl                  false
% 1.66/0.99  --smt_preprocessing                     true
% 1.66/0.99  --smt_ac_axioms                         fast
% 1.66/0.99  --preprocessed_out                      false
% 1.66/0.99  --preprocessed_stats                    false
% 1.66/0.99  
% 1.66/0.99  ------ Abstraction refinement Options
% 1.66/0.99  
% 1.66/0.99  --abstr_ref                             []
% 1.66/0.99  --abstr_ref_prep                        false
% 1.66/0.99  --abstr_ref_until_sat                   false
% 1.66/0.99  --abstr_ref_sig_restrict                funpre
% 1.66/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.66/0.99  --abstr_ref_under                       []
% 1.66/0.99  
% 1.66/0.99  ------ SAT Options
% 1.66/0.99  
% 1.66/0.99  --sat_mode                              false
% 1.66/0.99  --sat_fm_restart_options                ""
% 1.66/0.99  --sat_gr_def                            false
% 1.66/0.99  --sat_epr_types                         true
% 1.66/0.99  --sat_non_cyclic_types                  false
% 1.66/0.99  --sat_finite_models                     false
% 1.66/0.99  --sat_fm_lemmas                         false
% 1.66/0.99  --sat_fm_prep                           false
% 1.66/0.99  --sat_fm_uc_incr                        true
% 1.66/0.99  --sat_out_model                         small
% 1.66/0.99  --sat_out_clauses                       false
% 1.66/0.99  
% 1.66/0.99  ------ QBF Options
% 1.66/0.99  
% 1.66/0.99  --qbf_mode                              false
% 1.66/0.99  --qbf_elim_univ                         false
% 1.66/0.99  --qbf_dom_inst                          none
% 1.66/0.99  --qbf_dom_pre_inst                      false
% 1.66/0.99  --qbf_sk_in                             false
% 1.66/0.99  --qbf_pred_elim                         true
% 1.66/0.99  --qbf_split                             512
% 1.66/0.99  
% 1.66/0.99  ------ BMC1 Options
% 1.66/0.99  
% 1.66/0.99  --bmc1_incremental                      false
% 1.66/0.99  --bmc1_axioms                           reachable_all
% 1.66/0.99  --bmc1_min_bound                        0
% 1.66/0.99  --bmc1_max_bound                        -1
% 1.66/0.99  --bmc1_max_bound_default                -1
% 1.66/0.99  --bmc1_symbol_reachability              true
% 1.66/0.99  --bmc1_property_lemmas                  false
% 1.66/0.99  --bmc1_k_induction                      false
% 1.66/0.99  --bmc1_non_equiv_states                 false
% 1.66/0.99  --bmc1_deadlock                         false
% 1.66/0.99  --bmc1_ucm                              false
% 1.66/0.99  --bmc1_add_unsat_core                   none
% 1.66/0.99  --bmc1_unsat_core_children              false
% 1.66/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.66/0.99  --bmc1_out_stat                         full
% 1.66/0.99  --bmc1_ground_init                      false
% 1.66/0.99  --bmc1_pre_inst_next_state              false
% 1.66/0.99  --bmc1_pre_inst_state                   false
% 1.66/0.99  --bmc1_pre_inst_reach_state             false
% 1.66/0.99  --bmc1_out_unsat_core                   false
% 1.66/0.99  --bmc1_aig_witness_out                  false
% 1.66/0.99  --bmc1_verbose                          false
% 1.66/0.99  --bmc1_dump_clauses_tptp                false
% 1.66/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.66/0.99  --bmc1_dump_file                        -
% 1.66/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.66/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.66/0.99  --bmc1_ucm_extend_mode                  1
% 1.66/0.99  --bmc1_ucm_init_mode                    2
% 1.66/0.99  --bmc1_ucm_cone_mode                    none
% 1.66/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.66/0.99  --bmc1_ucm_relax_model                  4
% 1.66/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.66/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.66/0.99  --bmc1_ucm_layered_model                none
% 1.66/0.99  --bmc1_ucm_max_lemma_size               10
% 1.66/0.99  
% 1.66/0.99  ------ AIG Options
% 1.66/0.99  
% 1.66/0.99  --aig_mode                              false
% 1.66/0.99  
% 1.66/0.99  ------ Instantiation Options
% 1.66/0.99  
% 1.66/0.99  --instantiation_flag                    true
% 1.66/0.99  --inst_sos_flag                         false
% 1.66/0.99  --inst_sos_phase                        true
% 1.66/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.66/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.66/0.99  --inst_lit_sel_side                     num_symb
% 1.66/0.99  --inst_solver_per_active                1400
% 1.66/0.99  --inst_solver_calls_frac                1.
% 1.66/0.99  --inst_passive_queue_type               priority_queues
% 1.66/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.66/0.99  --inst_passive_queues_freq              [25;2]
% 1.66/0.99  --inst_dismatching                      true
% 1.66/0.99  --inst_eager_unprocessed_to_passive     true
% 1.66/0.99  --inst_prop_sim_given                   true
% 1.66/0.99  --inst_prop_sim_new                     false
% 1.66/0.99  --inst_subs_new                         false
% 1.66/0.99  --inst_eq_res_simp                      false
% 1.66/0.99  --inst_subs_given                       false
% 1.66/0.99  --inst_orphan_elimination               true
% 1.66/0.99  --inst_learning_loop_flag               true
% 1.66/0.99  --inst_learning_start                   3000
% 1.66/0.99  --inst_learning_factor                  2
% 1.66/0.99  --inst_start_prop_sim_after_learn       3
% 1.66/0.99  --inst_sel_renew                        solver
% 1.66/0.99  --inst_lit_activity_flag                true
% 1.66/0.99  --inst_restr_to_given                   false
% 1.66/0.99  --inst_activity_threshold               500
% 1.66/0.99  --inst_out_proof                        true
% 1.66/0.99  
% 1.66/0.99  ------ Resolution Options
% 1.66/0.99  
% 1.66/0.99  --resolution_flag                       true
% 1.66/0.99  --res_lit_sel                           adaptive
% 1.66/0.99  --res_lit_sel_side                      none
% 1.66/0.99  --res_ordering                          kbo
% 1.66/0.99  --res_to_prop_solver                    active
% 1.66/0.99  --res_prop_simpl_new                    false
% 1.66/0.99  --res_prop_simpl_given                  true
% 1.66/0.99  --res_passive_queue_type                priority_queues
% 1.66/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.66/0.99  --res_passive_queues_freq               [15;5]
% 1.66/0.99  --res_forward_subs                      full
% 1.66/0.99  --res_backward_subs                     full
% 1.66/0.99  --res_forward_subs_resolution           true
% 1.66/0.99  --res_backward_subs_resolution          true
% 1.66/0.99  --res_orphan_elimination                true
% 1.66/0.99  --res_time_limit                        2.
% 1.66/0.99  --res_out_proof                         true
% 1.66/0.99  
% 1.66/0.99  ------ Superposition Options
% 1.66/0.99  
% 1.66/0.99  --superposition_flag                    true
% 1.66/0.99  --sup_passive_queue_type                priority_queues
% 1.66/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.66/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.66/0.99  --demod_completeness_check              fast
% 1.66/0.99  --demod_use_ground                      true
% 1.66/0.99  --sup_to_prop_solver                    passive
% 1.66/0.99  --sup_prop_simpl_new                    true
% 1.66/0.99  --sup_prop_simpl_given                  true
% 1.66/0.99  --sup_fun_splitting                     false
% 1.66/0.99  --sup_smt_interval                      50000
% 1.66/0.99  
% 1.66/0.99  ------ Superposition Simplification Setup
% 1.66/0.99  
% 1.66/0.99  --sup_indices_passive                   []
% 1.66/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.66/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/0.99  --sup_full_bw                           [BwDemod]
% 1.66/0.99  --sup_immed_triv                        [TrivRules]
% 1.66/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.66/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/0.99  --sup_immed_bw_main                     []
% 1.66/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.66/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/0.99  
% 1.66/0.99  ------ Combination Options
% 1.66/0.99  
% 1.66/0.99  --comb_res_mult                         3
% 1.66/0.99  --comb_sup_mult                         2
% 1.66/0.99  --comb_inst_mult                        10
% 1.66/0.99  
% 1.66/0.99  ------ Debug Options
% 1.66/0.99  
% 1.66/0.99  --dbg_backtrace                         false
% 1.66/0.99  --dbg_dump_prop_clauses                 false
% 1.66/0.99  --dbg_dump_prop_clauses_file            -
% 1.66/0.99  --dbg_out_stat                          false
% 1.66/0.99  ------ Parsing...
% 1.66/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.66/0.99  
% 1.66/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 1.66/0.99  
% 1.66/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.66/0.99  
% 1.66/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.66/0.99  ------ Proving...
% 1.66/0.99  ------ Problem Properties 
% 1.66/0.99  
% 1.66/0.99  
% 1.66/0.99  clauses                                 19
% 1.66/0.99  conjectures                             6
% 1.66/0.99  EPR                                     1
% 1.66/0.99  Horn                                    18
% 1.66/0.99  unary                                   7
% 1.66/0.99  binary                                  3
% 1.66/0.99  lits                                    44
% 1.66/0.99  lits eq                                 4
% 1.66/0.99  fd_pure                                 0
% 1.66/0.99  fd_pseudo                               0
% 1.66/0.99  fd_cond                                 0
% 1.66/0.99  fd_pseudo_cond                          0
% 1.66/0.99  AC symbols                              0
% 1.66/0.99  
% 1.66/0.99  ------ Schedule dynamic 5 is on 
% 1.66/0.99  
% 1.66/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.66/0.99  
% 1.66/0.99  
% 1.66/0.99  ------ 
% 1.66/0.99  Current options:
% 1.66/0.99  ------ 
% 1.66/0.99  
% 1.66/0.99  ------ Input Options
% 1.66/0.99  
% 1.66/0.99  --out_options                           all
% 1.66/0.99  --tptp_safe_out                         true
% 1.66/0.99  --problem_path                          ""
% 1.66/0.99  --include_path                          ""
% 1.66/0.99  --clausifier                            res/vclausify_rel
% 1.66/0.99  --clausifier_options                    --mode clausify
% 1.66/0.99  --stdin                                 false
% 1.66/0.99  --stats_out                             all
% 1.66/0.99  
% 1.66/0.99  ------ General Options
% 1.66/0.99  
% 1.66/0.99  --fof                                   false
% 1.66/0.99  --time_out_real                         305.
% 1.66/0.99  --time_out_virtual                      -1.
% 1.66/0.99  --symbol_type_check                     false
% 1.66/0.99  --clausify_out                          false
% 1.66/0.99  --sig_cnt_out                           false
% 1.66/0.99  --trig_cnt_out                          false
% 1.66/0.99  --trig_cnt_out_tolerance                1.
% 1.66/0.99  --trig_cnt_out_sk_spl                   false
% 1.66/0.99  --abstr_cl_out                          false
% 1.66/0.99  
% 1.66/0.99  ------ Global Options
% 1.66/0.99  
% 1.66/0.99  --schedule                              default
% 1.66/0.99  --add_important_lit                     false
% 1.66/0.99  --prop_solver_per_cl                    1000
% 1.66/0.99  --min_unsat_core                        false
% 1.66/0.99  --soft_assumptions                      false
% 1.66/0.99  --soft_lemma_size                       3
% 1.66/0.99  --prop_impl_unit_size                   0
% 1.66/0.99  --prop_impl_unit                        []
% 1.66/0.99  --share_sel_clauses                     true
% 1.66/0.99  --reset_solvers                         false
% 1.66/0.99  --bc_imp_inh                            [conj_cone]
% 1.66/0.99  --conj_cone_tolerance                   3.
% 1.66/0.99  --extra_neg_conj                        none
% 1.66/0.99  --large_theory_mode                     true
% 1.66/0.99  --prolific_symb_bound                   200
% 1.66/0.99  --lt_threshold                          2000
% 1.66/0.99  --clause_weak_htbl                      true
% 1.66/0.99  --gc_record_bc_elim                     false
% 1.66/0.99  
% 1.66/0.99  ------ Preprocessing Options
% 1.66/0.99  
% 1.66/0.99  --preprocessing_flag                    true
% 1.66/0.99  --time_out_prep_mult                    0.1
% 1.66/0.99  --splitting_mode                        input
% 1.66/0.99  --splitting_grd                         true
% 1.66/0.99  --splitting_cvd                         false
% 1.66/0.99  --splitting_cvd_svl                     false
% 1.66/0.99  --splitting_nvd                         32
% 1.66/0.99  --sub_typing                            true
% 1.66/0.99  --prep_gs_sim                           true
% 1.66/0.99  --prep_unflatten                        true
% 1.66/0.99  --prep_res_sim                          true
% 1.66/0.99  --prep_upred                            true
% 1.66/0.99  --prep_sem_filter                       exhaustive
% 1.66/0.99  --prep_sem_filter_out                   false
% 1.66/0.99  --pred_elim                             true
% 1.66/0.99  --res_sim_input                         true
% 1.66/0.99  --eq_ax_congr_red                       true
% 1.66/0.99  --pure_diseq_elim                       true
% 1.66/0.99  --brand_transform                       false
% 1.66/0.99  --non_eq_to_eq                          false
% 1.66/0.99  --prep_def_merge                        true
% 1.66/0.99  --prep_def_merge_prop_impl              false
% 1.66/0.99  --prep_def_merge_mbd                    true
% 1.66/0.99  --prep_def_merge_tr_red                 false
% 1.66/0.99  --prep_def_merge_tr_cl                  false
% 1.66/0.99  --smt_preprocessing                     true
% 1.66/0.99  --smt_ac_axioms                         fast
% 1.66/0.99  --preprocessed_out                      false
% 1.66/0.99  --preprocessed_stats                    false
% 1.66/0.99  
% 1.66/0.99  ------ Abstraction refinement Options
% 1.66/0.99  
% 1.66/0.99  --abstr_ref                             []
% 1.66/0.99  --abstr_ref_prep                        false
% 1.66/0.99  --abstr_ref_until_sat                   false
% 1.66/0.99  --abstr_ref_sig_restrict                funpre
% 1.66/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.66/0.99  --abstr_ref_under                       []
% 1.66/0.99  
% 1.66/0.99  ------ SAT Options
% 1.66/0.99  
% 1.66/0.99  --sat_mode                              false
% 1.66/0.99  --sat_fm_restart_options                ""
% 1.66/0.99  --sat_gr_def                            false
% 1.66/0.99  --sat_epr_types                         true
% 1.66/0.99  --sat_non_cyclic_types                  false
% 1.66/0.99  --sat_finite_models                     false
% 1.66/0.99  --sat_fm_lemmas                         false
% 1.66/0.99  --sat_fm_prep                           false
% 1.66/0.99  --sat_fm_uc_incr                        true
% 1.66/0.99  --sat_out_model                         small
% 1.66/0.99  --sat_out_clauses                       false
% 1.66/0.99  
% 1.66/0.99  ------ QBF Options
% 1.66/0.99  
% 1.66/0.99  --qbf_mode                              false
% 1.66/0.99  --qbf_elim_univ                         false
% 1.66/0.99  --qbf_dom_inst                          none
% 1.66/0.99  --qbf_dom_pre_inst                      false
% 1.66/0.99  --qbf_sk_in                             false
% 1.66/0.99  --qbf_pred_elim                         true
% 1.66/0.99  --qbf_split                             512
% 1.66/0.99  
% 1.66/0.99  ------ BMC1 Options
% 1.66/0.99  
% 1.66/0.99  --bmc1_incremental                      false
% 1.66/0.99  --bmc1_axioms                           reachable_all
% 1.66/0.99  --bmc1_min_bound                        0
% 1.66/0.99  --bmc1_max_bound                        -1
% 1.66/0.99  --bmc1_max_bound_default                -1
% 1.66/0.99  --bmc1_symbol_reachability              true
% 1.66/0.99  --bmc1_property_lemmas                  false
% 1.66/0.99  --bmc1_k_induction                      false
% 1.66/0.99  --bmc1_non_equiv_states                 false
% 1.66/0.99  --bmc1_deadlock                         false
% 1.66/0.99  --bmc1_ucm                              false
% 1.66/0.99  --bmc1_add_unsat_core                   none
% 1.66/0.99  --bmc1_unsat_core_children              false
% 1.66/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.66/0.99  --bmc1_out_stat                         full
% 1.66/0.99  --bmc1_ground_init                      false
% 1.66/0.99  --bmc1_pre_inst_next_state              false
% 1.66/0.99  --bmc1_pre_inst_state                   false
% 1.66/0.99  --bmc1_pre_inst_reach_state             false
% 1.66/0.99  --bmc1_out_unsat_core                   false
% 1.66/0.99  --bmc1_aig_witness_out                  false
% 1.66/0.99  --bmc1_verbose                          false
% 1.66/0.99  --bmc1_dump_clauses_tptp                false
% 1.66/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.66/0.99  --bmc1_dump_file                        -
% 1.66/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.66/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.66/0.99  --bmc1_ucm_extend_mode                  1
% 1.66/0.99  --bmc1_ucm_init_mode                    2
% 1.66/0.99  --bmc1_ucm_cone_mode                    none
% 1.66/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.66/0.99  --bmc1_ucm_relax_model                  4
% 1.66/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.66/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.66/0.99  --bmc1_ucm_layered_model                none
% 1.66/0.99  --bmc1_ucm_max_lemma_size               10
% 1.66/0.99  
% 1.66/0.99  ------ AIG Options
% 1.66/0.99  
% 1.66/0.99  --aig_mode                              false
% 1.66/0.99  
% 1.66/0.99  ------ Instantiation Options
% 1.66/0.99  
% 1.66/0.99  --instantiation_flag                    true
% 1.66/0.99  --inst_sos_flag                         false
% 1.66/0.99  --inst_sos_phase                        true
% 1.66/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.66/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.66/0.99  --inst_lit_sel_side                     none
% 1.66/0.99  --inst_solver_per_active                1400
% 1.66/0.99  --inst_solver_calls_frac                1.
% 1.66/0.99  --inst_passive_queue_type               priority_queues
% 1.66/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.66/0.99  --inst_passive_queues_freq              [25;2]
% 1.66/0.99  --inst_dismatching                      true
% 1.66/0.99  --inst_eager_unprocessed_to_passive     true
% 1.66/0.99  --inst_prop_sim_given                   true
% 1.66/0.99  --inst_prop_sim_new                     false
% 1.66/0.99  --inst_subs_new                         false
% 1.66/0.99  --inst_eq_res_simp                      false
% 1.66/0.99  --inst_subs_given                       false
% 1.66/0.99  --inst_orphan_elimination               true
% 1.66/0.99  --inst_learning_loop_flag               true
% 1.66/0.99  --inst_learning_start                   3000
% 1.66/0.99  --inst_learning_factor                  2
% 1.66/0.99  --inst_start_prop_sim_after_learn       3
% 1.66/0.99  --inst_sel_renew                        solver
% 1.66/0.99  --inst_lit_activity_flag                true
% 1.66/0.99  --inst_restr_to_given                   false
% 1.66/0.99  --inst_activity_threshold               500
% 1.66/0.99  --inst_out_proof                        true
% 1.66/0.99  
% 1.66/0.99  ------ Resolution Options
% 1.66/0.99  
% 1.66/0.99  --resolution_flag                       false
% 1.66/0.99  --res_lit_sel                           adaptive
% 1.66/0.99  --res_lit_sel_side                      none
% 1.66/0.99  --res_ordering                          kbo
% 1.66/0.99  --res_to_prop_solver                    active
% 1.66/0.99  --res_prop_simpl_new                    false
% 1.66/0.99  --res_prop_simpl_given                  true
% 1.66/0.99  --res_passive_queue_type                priority_queues
% 1.66/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.66/0.99  --res_passive_queues_freq               [15;5]
% 1.66/0.99  --res_forward_subs                      full
% 1.66/0.99  --res_backward_subs                     full
% 1.66/0.99  --res_forward_subs_resolution           true
% 1.66/0.99  --res_backward_subs_resolution          true
% 1.66/0.99  --res_orphan_elimination                true
% 1.66/0.99  --res_time_limit                        2.
% 1.66/0.99  --res_out_proof                         true
% 1.66/0.99  
% 1.66/0.99  ------ Superposition Options
% 1.66/0.99  
% 1.66/0.99  --superposition_flag                    true
% 1.66/0.99  --sup_passive_queue_type                priority_queues
% 1.66/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.66/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.66/0.99  --demod_completeness_check              fast
% 1.66/0.99  --demod_use_ground                      true
% 1.66/0.99  --sup_to_prop_solver                    passive
% 1.66/0.99  --sup_prop_simpl_new                    true
% 1.66/0.99  --sup_prop_simpl_given                  true
% 1.66/0.99  --sup_fun_splitting                     false
% 1.66/0.99  --sup_smt_interval                      50000
% 1.66/0.99  
% 1.66/0.99  ------ Superposition Simplification Setup
% 1.66/0.99  
% 1.66/0.99  --sup_indices_passive                   []
% 1.66/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.66/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/0.99  --sup_full_bw                           [BwDemod]
% 1.66/0.99  --sup_immed_triv                        [TrivRules]
% 1.66/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.66/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/0.99  --sup_immed_bw_main                     []
% 1.66/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.66/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/0.99  
% 1.66/0.99  ------ Combination Options
% 1.66/0.99  
% 1.66/0.99  --comb_res_mult                         3
% 1.66/0.99  --comb_sup_mult                         2
% 1.66/0.99  --comb_inst_mult                        10
% 1.66/0.99  
% 1.66/0.99  ------ Debug Options
% 1.66/0.99  
% 1.66/0.99  --dbg_backtrace                         false
% 1.66/0.99  --dbg_dump_prop_clauses                 false
% 1.66/0.99  --dbg_dump_prop_clauses_file            -
% 1.66/0.99  --dbg_out_stat                          false
% 1.66/0.99  
% 1.66/0.99  
% 1.66/0.99  
% 1.66/0.99  
% 1.66/0.99  ------ Proving...
% 1.66/0.99  
% 1.66/0.99  
% 1.66/0.99  % SZS status Theorem for theBenchmark.p
% 1.66/0.99  
% 1.66/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.66/0.99  
% 1.66/0.99  fof(f16,conjecture,(
% 1.66/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.99  
% 1.66/0.99  fof(f17,negated_conjecture,(
% 1.66/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.66/0.99    inference(negated_conjecture,[],[f16])).
% 1.66/0.99  
% 1.66/0.99  fof(f41,plain,(
% 1.66/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.66/0.99    inference(ennf_transformation,[],[f17])).
% 1.66/0.99  
% 1.66/0.99  fof(f42,plain,(
% 1.66/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.66/0.99    inference(flattening,[],[f41])).
% 1.66/0.99  
% 1.66/0.99  fof(f46,plain,(
% 1.66/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.66/0.99    inference(nnf_transformation,[],[f42])).
% 1.66/0.99  
% 1.66/0.99  fof(f47,plain,(
% 1.66/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.66/0.99    inference(flattening,[],[f46])).
% 1.66/0.99  
% 1.66/0.99  fof(f53,plain,(
% 1.66/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5) | r1_tmap_1(X1,X0,X2,X4)) & sK5 = X4 & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 1.66/0.99    introduced(choice_axiom,[])).
% 1.66/0.99  
% 1.66/0.99  fof(f52,plain,(
% 1.66/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 1.66/0.99    introduced(choice_axiom,[])).
% 1.66/0.99  
% 1.66/0.99  fof(f51,plain,(
% 1.66/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK3,X1) & v1_tsep_1(sK3,X1) & ~v2_struct_0(sK3))) )),
% 1.66/0.99    introduced(choice_axiom,[])).
% 1.66/0.99  
% 1.66/0.99  fof(f50,plain,(
% 1.66/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5) | ~r1_tmap_1(X1,X0,sK2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5) | r1_tmap_1(X1,X0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK2))) )),
% 1.66/0.99    introduced(choice_axiom,[])).
% 1.66/0.99  
% 1.66/0.99  fof(f49,plain,(
% 1.66/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5) | ~r1_tmap_1(sK1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5) | r1_tmap_1(sK1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.66/0.99    introduced(choice_axiom,[])).
% 1.66/0.99  
% 1.66/0.99  fof(f48,plain,(
% 1.66/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.66/0.99    introduced(choice_axiom,[])).
% 1.66/0.99  
% 1.66/0.99  fof(f54,plain,(
% 1.66/0.99    ((((((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.66/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f47,f53,f52,f51,f50,f49,f48])).
% 1.66/0.99  
% 1.66/0.99  fof(f88,plain,(
% 1.66/0.99    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 1.66/0.99    inference(cnf_transformation,[],[f54])).
% 1.66/0.99  
% 1.66/0.99  fof(f87,plain,(
% 1.66/0.99    sK4 = sK5),
% 1.66/0.99    inference(cnf_transformation,[],[f54])).
% 1.66/0.99  
% 1.66/0.99  fof(f89,plain,(
% 1.66/0.99    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 1.66/0.99    inference(cnf_transformation,[],[f54])).
% 1.66/0.99  
% 1.66/0.99  fof(f86,plain,(
% 1.66/0.99    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.66/0.99    inference(cnf_transformation,[],[f54])).
% 1.66/0.99  
% 1.66/0.99  fof(f84,plain,(
% 1.66/0.99    m1_pre_topc(sK3,sK1)),
% 1.66/0.99    inference(cnf_transformation,[],[f54])).
% 1.66/0.99  
% 1.66/0.99  fof(f15,axiom,(
% 1.66/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.99  
% 1.66/0.99  fof(f39,plain,(
% 1.66/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.99    inference(ennf_transformation,[],[f15])).
% 1.66/0.99  
% 1.66/0.99  fof(f40,plain,(
% 1.66/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.99    inference(flattening,[],[f39])).
% 1.66/0.99  
% 1.66/0.99  fof(f45,plain,(
% 1.66/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.99    inference(nnf_transformation,[],[f40])).
% 1.66/0.99  
% 1.66/0.99  fof(f71,plain,(
% 1.66/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.99    inference(cnf_transformation,[],[f45])).
% 1.66/0.99  
% 1.66/0.99  fof(f95,plain,(
% 1.66/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.99    inference(equality_resolution,[],[f71])).
% 1.66/0.99  
% 1.66/0.99  fof(f14,axiom,(
% 1.66/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 1.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.99  
% 1.66/0.99  fof(f37,plain,(
% 1.66/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.99    inference(ennf_transformation,[],[f14])).
% 1.66/0.99  
% 1.66/0.99  fof(f38,plain,(
% 1.66/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.99    inference(flattening,[],[f37])).
% 1.66/0.99  
% 1.66/0.99  fof(f70,plain,(
% 1.66/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.99    inference(cnf_transformation,[],[f38])).
% 1.66/0.99  
% 1.66/0.99  fof(f93,plain,(
% 1.66/0.99    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.99    inference(equality_resolution,[],[f70])).
% 1.66/0.99  
% 1.66/0.99  fof(f80,plain,(
% 1.66/0.99    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.66/0.99    inference(cnf_transformation,[],[f54])).
% 1.66/0.99  
% 1.66/0.99  fof(f79,plain,(
% 1.66/0.99    v1_funct_1(sK2)),
% 1.66/0.99    inference(cnf_transformation,[],[f54])).
% 1.66/0.99  
% 1.66/0.99  fof(f9,axiom,(
% 1.66/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.99  
% 1.66/0.99  fof(f28,plain,(
% 1.66/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.99    inference(ennf_transformation,[],[f9])).
% 1.66/0.99  
% 1.66/0.99  fof(f29,plain,(
% 1.66/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.99    inference(flattening,[],[f28])).
% 1.66/0.99  
% 1.66/0.99  fof(f63,plain,(
% 1.66/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.99    inference(cnf_transformation,[],[f29])).
% 1.66/0.99  
% 1.66/0.99  fof(f76,plain,(
% 1.66/0.99    ~v2_struct_0(sK1)),
% 1.66/0.99    inference(cnf_transformation,[],[f54])).
% 1.66/0.99  
% 1.66/0.99  fof(f77,plain,(
% 1.66/0.99    v2_pre_topc(sK1)),
% 1.66/0.99    inference(cnf_transformation,[],[f54])).
% 1.66/0.99  
% 1.66/0.99  fof(f78,plain,(
% 1.66/0.99    l1_pre_topc(sK1)),
% 1.66/0.99    inference(cnf_transformation,[],[f54])).
% 1.66/0.99  
% 1.66/0.99  fof(f82,plain,(
% 1.66/0.99    ~v2_struct_0(sK3)),
% 1.66/0.99    inference(cnf_transformation,[],[f54])).
% 1.66/0.99  
% 1.66/0.99  fof(f74,plain,(
% 1.66/0.99    v2_pre_topc(sK0)),
% 1.66/0.99    inference(cnf_transformation,[],[f54])).
% 1.66/0.99  
% 1.66/0.99  fof(f73,plain,(
% 1.66/0.99    ~v2_struct_0(sK0)),
% 1.66/0.99    inference(cnf_transformation,[],[f54])).
% 1.66/0.99  
% 1.66/0.99  fof(f75,plain,(
% 1.66/0.99    l1_pre_topc(sK0)),
% 1.66/0.99    inference(cnf_transformation,[],[f54])).
% 1.66/0.99  
% 1.66/0.99  fof(f81,plain,(
% 1.66/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.66/0.99    inference(cnf_transformation,[],[f54])).
% 1.66/0.99  
% 1.66/0.99  fof(f6,axiom,(
% 1.66/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.99  
% 1.66/0.99  fof(f24,plain,(
% 1.66/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.66/0.99    inference(ennf_transformation,[],[f6])).
% 1.66/0.99  
% 1.66/0.99  fof(f60,plain,(
% 1.66/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.66/0.99    inference(cnf_transformation,[],[f24])).
% 1.66/0.99  
% 1.66/0.99  fof(f8,axiom,(
% 1.66/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.99  
% 1.66/0.99  fof(f26,plain,(
% 1.66/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.66/0.99    inference(ennf_transformation,[],[f8])).
% 1.66/0.99  
% 1.66/0.99  fof(f27,plain,(
% 1.66/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.66/0.99    inference(flattening,[],[f26])).
% 1.66/0.99  
% 1.66/0.99  fof(f62,plain,(
% 1.66/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.66/0.99    inference(cnf_transformation,[],[f27])).
% 1.66/0.99  
% 1.66/0.99  fof(f7,axiom,(
% 1.66/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.99  
% 1.66/0.99  fof(f25,plain,(
% 1.66/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.66/0.99    inference(ennf_transformation,[],[f7])).
% 1.66/0.99  
% 1.66/0.99  fof(f61,plain,(
% 1.66/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.66/0.99    inference(cnf_transformation,[],[f25])).
% 1.66/0.99  
% 1.66/0.99  fof(f4,axiom,(
% 1.66/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.99  
% 1.66/0.99  fof(f18,plain,(
% 1.66/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 1.66/0.99    inference(unused_predicate_definition_removal,[],[f4])).
% 1.66/0.99  
% 1.66/0.99  fof(f21,plain,(
% 1.66/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.66/0.99    inference(ennf_transformation,[],[f18])).
% 1.66/0.99  
% 1.66/0.99  fof(f58,plain,(
% 1.66/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.66/0.99    inference(cnf_transformation,[],[f21])).
% 1.66/0.99  
% 1.66/0.99  fof(f72,plain,(
% 1.66/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.99    inference(cnf_transformation,[],[f45])).
% 1.66/0.99  
% 1.66/0.99  fof(f94,plain,(
% 1.66/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.99    inference(equality_resolution,[],[f72])).
% 1.66/0.99  
% 1.66/0.99  fof(f3,axiom,(
% 1.66/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.99  
% 1.66/0.99  fof(f19,plain,(
% 1.66/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.66/0.99    inference(ennf_transformation,[],[f3])).
% 1.66/0.99  
% 1.66/0.99  fof(f20,plain,(
% 1.66/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.66/0.99    inference(flattening,[],[f19])).
% 1.66/0.99  
% 1.66/0.99  fof(f57,plain,(
% 1.66/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.66/0.99    inference(cnf_transformation,[],[f20])).
% 1.66/0.99  
% 1.66/0.99  fof(f11,axiom,(
% 1.66/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.99  
% 1.66/0.99  fof(f32,plain,(
% 1.66/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.99    inference(ennf_transformation,[],[f11])).
% 1.66/0.99  
% 1.66/0.99  fof(f33,plain,(
% 1.66/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.99    inference(flattening,[],[f32])).
% 1.66/0.99  
% 1.66/0.99  fof(f65,plain,(
% 1.66/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.99    inference(cnf_transformation,[],[f33])).
% 1.66/0.99  
% 1.66/0.99  fof(f12,axiom,(
% 1.66/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.99  
% 1.66/0.99  fof(f34,plain,(
% 1.66/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.66/0.99    inference(ennf_transformation,[],[f12])).
% 1.66/0.99  
% 1.66/0.99  fof(f35,plain,(
% 1.66/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.66/0.99    inference(flattening,[],[f34])).
% 1.66/0.99  
% 1.66/0.99  fof(f43,plain,(
% 1.66/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.66/0.99    inference(nnf_transformation,[],[f35])).
% 1.66/0.99  
% 1.66/0.99  fof(f44,plain,(
% 1.66/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.66/0.99    inference(flattening,[],[f43])).
% 1.66/0.99  
% 1.66/0.99  fof(f66,plain,(
% 1.66/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.66/0.99    inference(cnf_transformation,[],[f44])).
% 1.66/0.99  
% 1.66/0.99  fof(f92,plain,(
% 1.66/0.99    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.66/0.99    inference(equality_resolution,[],[f66])).
% 1.66/0.99  
% 1.66/0.99  fof(f13,axiom,(
% 1.66/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.99  
% 1.66/0.99  fof(f36,plain,(
% 1.66/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.66/0.99    inference(ennf_transformation,[],[f13])).
% 1.66/0.99  
% 1.66/0.99  fof(f69,plain,(
% 1.66/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.66/0.99    inference(cnf_transformation,[],[f36])).
% 1.66/0.99  
% 1.66/0.99  fof(f83,plain,(
% 1.66/0.99    v1_tsep_1(sK3,sK1)),
% 1.66/0.99    inference(cnf_transformation,[],[f54])).
% 1.66/0.99  
% 1.66/0.99  fof(f5,axiom,(
% 1.66/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.99  
% 1.66/0.99  fof(f22,plain,(
% 1.66/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.66/0.99    inference(ennf_transformation,[],[f5])).
% 1.66/0.99  
% 1.66/0.99  fof(f23,plain,(
% 1.66/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.66/0.99    inference(flattening,[],[f22])).
% 1.66/0.99  
% 1.66/0.99  fof(f59,plain,(
% 1.66/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.66/0.99    inference(cnf_transformation,[],[f23])).
% 1.66/0.99  
% 1.66/0.99  fof(f2,axiom,(
% 1.66/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.99  
% 1.66/0.99  fof(f56,plain,(
% 1.66/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.66/0.99    inference(cnf_transformation,[],[f2])).
% 1.66/0.99  
% 1.66/0.99  fof(f1,axiom,(
% 1.66/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 1.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.99  
% 1.66/0.99  fof(f55,plain,(
% 1.66/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.66/0.99    inference(cnf_transformation,[],[f1])).
% 1.66/0.99  
% 1.66/0.99  cnf(c_19,negated_conjecture,
% 1.66/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK4)
% 1.66/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.66/0.99      inference(cnf_transformation,[],[f88]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_2083,plain,
% 1.66/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK4) = iProver_top
% 1.66/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
% 1.66/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_20,negated_conjecture,
% 1.66/0.99      ( sK4 = sK5 ),
% 1.66/0.99      inference(cnf_transformation,[],[f87]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_2106,plain,
% 1.66/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
% 1.66/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
% 1.66/0.99      inference(light_normalisation,[status(thm)],[c_2083,c_20]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_18,negated_conjecture,
% 1.66/0.99      ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
% 1.66/0.99      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.66/0.99      inference(cnf_transformation,[],[f89]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_2084,plain,
% 1.66/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK4) != iProver_top
% 1.66/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
% 1.66/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_2111,plain,
% 1.66/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
% 1.66/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
% 1.66/0.99      inference(light_normalisation,[status(thm)],[c_2084,c_20]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_21,negated_conjecture,
% 1.66/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 1.66/0.99      inference(cnf_transformation,[],[f86]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_48,plain,
% 1.66/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 1.66/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_23,negated_conjecture,
% 1.66/0.99      ( m1_pre_topc(sK3,sK1) ),
% 1.66/0.99      inference(cnf_transformation,[],[f84]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_17,plain,
% 1.66/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.66/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.66/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.66/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 1.66/0.99      | ~ m1_pre_topc(X4,X0)
% 1.66/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.66/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.66/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.66/0.99      | ~ v1_funct_1(X2)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | ~ v2_pre_topc(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X4)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | ~ l1_pre_topc(X0) ),
% 1.66/0.99      inference(cnf_transformation,[],[f95]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_15,plain,
% 1.66/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.66/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.66/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.66/0.99      | ~ m1_pre_topc(X4,X0)
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.66/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.66/0.99      | ~ v1_funct_1(X2)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | ~ v2_pre_topc(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X4)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | ~ l1_pre_topc(X0) ),
% 1.66/0.99      inference(cnf_transformation,[],[f93]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_180,plain,
% 1.66/0.99      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.66/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.66/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.66/0.99      | ~ r1_tmap_1(X0,X1,X2,X3)
% 1.66/0.99      | ~ m1_pre_topc(X4,X0)
% 1.66/0.99      | ~ v1_funct_1(X2)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | ~ v2_pre_topc(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X4)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | ~ l1_pre_topc(X0) ),
% 1.66/0.99      inference(global_propositional_subsumption,
% 1.66/0.99                [status(thm)],
% 1.66/0.99                [c_17,c_15]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_181,plain,
% 1.66/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.66/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.66/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.66/0.99      | ~ m1_pre_topc(X4,X0)
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.66/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.66/0.99      | ~ v1_funct_1(X2)
% 1.66/0.99      | ~ v2_pre_topc(X0)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | v2_struct_0(X4)
% 1.66/0.99      | ~ l1_pre_topc(X0)
% 1.66/0.99      | ~ l1_pre_topc(X1) ),
% 1.66/0.99      inference(renaming,[status(thm)],[c_180]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_27,negated_conjecture,
% 1.66/0.99      ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 1.66/0.99      inference(cnf_transformation,[],[f80]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_816,plain,
% 1.66/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.66/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.66/0.99      | ~ m1_pre_topc(X4,X0)
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.66/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.66/0.99      | ~ v1_funct_1(X2)
% 1.66/0.99      | ~ v2_pre_topc(X0)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | v2_struct_0(X4)
% 1.66/0.99      | ~ l1_pre_topc(X0)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.66/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.66/0.99      | sK2 != X2 ),
% 1.66/0.99      inference(resolution_lifted,[status(thm)],[c_181,c_27]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_817,plain,
% 1.66/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.66/0.99      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.66/0.99      | ~ m1_pre_topc(X0,X2)
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.66/0.99      | ~ v1_funct_1(sK2)
% 1.66/0.99      | ~ v2_pre_topc(X2)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | v2_struct_0(X2)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | ~ l1_pre_topc(X2)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.66/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.66/0.99      inference(unflattening,[status(thm)],[c_816]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_28,negated_conjecture,
% 1.66/0.99      ( v1_funct_1(sK2) ),
% 1.66/0.99      inference(cnf_transformation,[],[f79]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_821,plain,
% 1.66/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.66/0.99      | ~ m1_pre_topc(X0,X2)
% 1.66/0.99      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.66/0.99      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.66/0.99      | ~ v2_pre_topc(X2)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | v2_struct_0(X2)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | ~ l1_pre_topc(X2)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.66/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.66/0.99      inference(global_propositional_subsumption,
% 1.66/0.99                [status(thm)],
% 1.66/0.99                [c_817,c_28]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_822,plain,
% 1.66/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.66/0.99      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.66/0.99      | ~ m1_pre_topc(X0,X2)
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | ~ v2_pre_topc(X2)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | v2_struct_0(X2)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | ~ l1_pre_topc(X2)
% 1.66/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.66/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.66/0.99      inference(renaming,[status(thm)],[c_821]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_8,plain,
% 1.66/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.66/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.66/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | ~ l1_pre_topc(X1) ),
% 1.66/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_857,plain,
% 1.66/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.66/0.99      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.66/0.99      | ~ m1_pre_topc(X0,X2)
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | ~ v2_pre_topc(X2)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | v2_struct_0(X2)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | ~ l1_pre_topc(X2)
% 1.66/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.66/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.66/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_822,c_8]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1089,plain,
% 1.66/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.66/0.99      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.66/0.99      | ~ v2_pre_topc(X2)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X2)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | ~ l1_pre_topc(X2)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.66/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.66/0.99      | sK1 != X2
% 1.66/0.99      | sK3 != X0 ),
% 1.66/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_857]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1090,plain,
% 1.66/0.99      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.66/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.66/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.66/0.99      | ~ v2_pre_topc(X0)
% 1.66/0.99      | ~ v2_pre_topc(sK1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(sK1)
% 1.66/0.99      | v2_struct_0(sK3)
% 1.66/0.99      | ~ l1_pre_topc(X0)
% 1.66/0.99      | ~ l1_pre_topc(sK1)
% 1.66/0.99      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.66/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.66/0.99      inference(unflattening,[status(thm)],[c_1089]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_31,negated_conjecture,
% 1.66/0.99      ( ~ v2_struct_0(sK1) ),
% 1.66/0.99      inference(cnf_transformation,[],[f76]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_30,negated_conjecture,
% 1.66/0.99      ( v2_pre_topc(sK1) ),
% 1.66/0.99      inference(cnf_transformation,[],[f77]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_29,negated_conjecture,
% 1.66/0.99      ( l1_pre_topc(sK1) ),
% 1.66/0.99      inference(cnf_transformation,[],[f78]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_25,negated_conjecture,
% 1.66/0.99      ( ~ v2_struct_0(sK3) ),
% 1.66/0.99      inference(cnf_transformation,[],[f82]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1094,plain,
% 1.66/0.99      ( ~ l1_pre_topc(X0)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.66/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.66/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.66/0.99      | ~ v2_pre_topc(X0)
% 1.66/0.99      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.66/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.66/0.99      inference(global_propositional_subsumption,
% 1.66/0.99                [status(thm)],
% 1.66/0.99                [c_1090,c_31,c_30,c_29,c_25]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1095,plain,
% 1.66/0.99      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.66/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.66/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.66/0.99      | ~ v2_pre_topc(X0)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | ~ l1_pre_topc(X0)
% 1.66/0.99      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.66/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.66/0.99      inference(renaming,[status(thm)],[c_1094]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_33,negated_conjecture,
% 1.66/0.99      ( v2_pre_topc(sK0) ),
% 1.66/0.99      inference(cnf_transformation,[],[f74]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1353,plain,
% 1.66/0.99      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.66/0.99      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.66/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | ~ l1_pre_topc(X0)
% 1.66/0.99      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.66/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.66/0.99      | sK0 != X0 ),
% 1.66/0.99      inference(resolution_lifted,[status(thm)],[c_1095,c_33]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1354,plain,
% 1.66/0.99      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
% 1.66/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.66/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.66/0.99      | v2_struct_0(sK0)
% 1.66/0.99      | ~ l1_pre_topc(sK0)
% 1.66/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.66/0.99      inference(unflattening,[status(thm)],[c_1353]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_34,negated_conjecture,
% 1.66/0.99      ( ~ v2_struct_0(sK0) ),
% 1.66/0.99      inference(cnf_transformation,[],[f73]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_32,negated_conjecture,
% 1.66/0.99      ( l1_pre_topc(sK0) ),
% 1.66/0.99      inference(cnf_transformation,[],[f75]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_26,negated_conjecture,
% 1.66/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 1.66/0.99      inference(cnf_transformation,[],[f81]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1358,plain,
% 1.66/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.66/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.66/0.99      | ~ r1_tmap_1(sK1,sK0,sK2,X0)
% 1.66/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.66/0.99      inference(global_propositional_subsumption,
% 1.66/0.99                [status(thm)],
% 1.66/0.99                [c_1354,c_34,c_32,c_26]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1359,plain,
% 1.66/0.99      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
% 1.66/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.66/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.66/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.66/0.99      inference(renaming,[status(thm)],[c_1358]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1530,plain,
% 1.66/0.99      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
% 1.66/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.66/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.66/0.99      inference(equality_resolution_simp,[status(thm)],[c_1359]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_2224,plain,
% 1.66/0.99      ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.66/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.66/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 1.66/0.99      inference(instantiation,[status(thm)],[c_1530]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_2225,plain,
% 1.66/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
% 1.66/0.99      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top
% 1.66/0.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 1.66/0.99      inference(predicate_to_equality,[status(thm)],[c_2224]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_2286,plain,
% 1.66/0.99      ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top ),
% 1.66/0.99      inference(global_propositional_subsumption,
% 1.66/0.99                [status(thm)],
% 1.66/0.99                [c_2111,c_48,c_2225]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_2292,plain,
% 1.66/0.99      ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
% 1.66/0.99      inference(global_propositional_subsumption,
% 1.66/0.99                [status(thm)],
% 1.66/0.99                [c_2106,c_48,c_2111,c_2225]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_5,plain,
% 1.66/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.66/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_7,plain,
% 1.66/0.99      ( v2_struct_0(X0)
% 1.66/0.99      | ~ l1_struct_0(X0)
% 1.66/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.66/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_436,plain,
% 1.66/0.99      ( v2_struct_0(X0)
% 1.66/0.99      | ~ l1_pre_topc(X0)
% 1.66/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.66/0.99      inference(resolution,[status(thm)],[c_5,c_7]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_6,plain,
% 1.66/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.66/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1078,plain,
% 1.66/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK1 != X0 | sK3 != X1 ),
% 1.66/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1079,plain,
% 1.66/0.99      ( ~ l1_pre_topc(sK1) | l1_pre_topc(sK3) ),
% 1.66/0.99      inference(unflattening,[status(thm)],[c_1078]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1081,plain,
% 1.66/0.99      ( l1_pre_topc(sK3) ),
% 1.66/0.99      inference(global_propositional_subsumption,
% 1.66/0.99                [status(thm)],
% 1.66/0.99                [c_1079,c_29]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1425,plain,
% 1.66/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 1.66/0.99      inference(resolution_lifted,[status(thm)],[c_436,c_1081]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1426,plain,
% 1.66/0.99      ( v2_struct_0(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.66/0.99      inference(unflattening,[status(thm)],[c_1425]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1428,plain,
% 1.66/0.99      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.66/0.99      inference(global_propositional_subsumption,
% 1.66/0.99                [status(thm)],
% 1.66/0.99                [c_1426,c_25]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_3,plain,
% 1.66/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.66/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_16,plain,
% 1.66/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.66/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.66/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.66/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 1.66/0.99      | ~ m1_pre_topc(X4,X0)
% 1.66/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.66/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.66/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.66/0.99      | ~ v1_funct_1(X2)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | ~ v2_pre_topc(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X4)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | ~ l1_pre_topc(X0) ),
% 1.66/0.99      inference(cnf_transformation,[],[f94]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_618,plain,
% 1.66/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.66/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.66/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.66/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 1.66/0.99      | ~ m1_pre_topc(X4,X0)
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.66/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
% 1.66/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.66/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.66/0.99      | ~ v1_funct_1(X2)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | ~ v2_pre_topc(X0)
% 1.66/0.99      | v2_struct_0(X4)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | ~ l1_pre_topc(X0)
% 1.66/0.99      | X5 != X6
% 1.66/0.99      | u1_struct_0(X4) != X7 ),
% 1.66/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_619,plain,
% 1.66/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.66/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.66/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.66/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 1.66/0.99      | ~ m1_pre_topc(X4,X0)
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.66/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.66/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.66/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
% 1.66/0.99      | ~ v1_funct_1(X2)
% 1.66/0.99      | ~ v2_pre_topc(X0)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | v2_struct_0(X4)
% 1.66/0.99      | ~ l1_pre_topc(X0)
% 1.66/0.99      | ~ l1_pre_topc(X1) ),
% 1.66/0.99      inference(unflattening,[status(thm)],[c_618]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_659,plain,
% 1.66/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.66/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.66/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.66/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 1.66/0.99      | ~ m1_pre_topc(X4,X0)
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.66/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.66/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.66/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
% 1.66/0.99      | ~ v1_funct_1(X2)
% 1.66/0.99      | ~ v2_pre_topc(X0)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | v2_struct_0(X4)
% 1.66/0.99      | ~ l1_pre_topc(X0)
% 1.66/0.99      | ~ l1_pre_topc(X1) ),
% 1.66/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_619,c_8]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_2,plain,
% 1.66/0.99      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 1.66/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_10,plain,
% 1.66/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.66/0.99      | ~ v3_pre_topc(X0,X1)
% 1.66/0.99      | ~ r2_hidden(X2,X0)
% 1.66/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | ~ l1_pre_topc(X1) ),
% 1.66/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_13,plain,
% 1.66/0.99      ( ~ v1_tsep_1(X0,X1)
% 1.66/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.66/0.99      | ~ m1_pre_topc(X0,X1)
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | ~ l1_pre_topc(X1) ),
% 1.66/0.99      inference(cnf_transformation,[],[f92]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_14,plain,
% 1.66/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.66/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/0.99      | ~ l1_pre_topc(X1) ),
% 1.66/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_188,plain,
% 1.66/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.66/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.66/0.99      | ~ v1_tsep_1(X0,X1)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | ~ l1_pre_topc(X1) ),
% 1.66/0.99      inference(global_propositional_subsumption,
% 1.66/0.99                [status(thm)],
% 1.66/0.99                [c_13,c_14]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_189,plain,
% 1.66/0.99      ( ~ v1_tsep_1(X0,X1)
% 1.66/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.66/0.99      | ~ m1_pre_topc(X0,X1)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | ~ l1_pre_topc(X1) ),
% 1.66/0.99      inference(renaming,[status(thm)],[c_188]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_24,negated_conjecture,
% 1.66/0.99      ( v1_tsep_1(sK3,sK1) ),
% 1.66/0.99      inference(cnf_transformation,[],[f83]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_477,plain,
% 1.66/0.99      ( v3_pre_topc(u1_struct_0(X0),X1)
% 1.66/0.99      | ~ m1_pre_topc(X0,X1)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | sK1 != X1
% 1.66/0.99      | sK3 != X0 ),
% 1.66/0.99      inference(resolution_lifted,[status(thm)],[c_189,c_24]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_478,plain,
% 1.66/0.99      ( v3_pre_topc(u1_struct_0(sK3),sK1)
% 1.66/0.99      | ~ m1_pre_topc(sK3,sK1)
% 1.66/0.99      | ~ v2_pre_topc(sK1)
% 1.66/0.99      | ~ l1_pre_topc(sK1) ),
% 1.66/0.99      inference(unflattening,[status(thm)],[c_477]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_480,plain,
% 1.66/0.99      ( v3_pre_topc(u1_struct_0(sK3),sK1) ),
% 1.66/0.99      inference(global_propositional_subsumption,
% 1.66/0.99                [status(thm)],
% 1.66/0.99                [c_478,c_30,c_29,c_23]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_490,plain,
% 1.66/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.66/0.99      | ~ r2_hidden(X2,X0)
% 1.66/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | u1_struct_0(sK3) != X0
% 1.66/0.99      | sK1 != X1 ),
% 1.66/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_480]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_491,plain,
% 1.66/0.99      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
% 1.66/0.99      | ~ r2_hidden(X0,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.66/0.99      | ~ v2_pre_topc(sK1)
% 1.66/0.99      | v2_struct_0(sK1)
% 1.66/0.99      | ~ l1_pre_topc(sK1) ),
% 1.66/0.99      inference(unflattening,[status(thm)],[c_490]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_495,plain,
% 1.66/0.99      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.66/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.66/0.99      | ~ r2_hidden(X0,u1_struct_0(sK3))
% 1.66/0.99      | m1_connsp_2(u1_struct_0(sK3),sK1,X0) ),
% 1.66/0.99      inference(global_propositional_subsumption,
% 1.66/0.99                [status(thm)],
% 1.66/0.99                [c_491,c_31,c_30,c_29]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_496,plain,
% 1.66/0.99      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
% 1.66/0.99      | ~ r2_hidden(X0,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.66/0.99      inference(renaming,[status(thm)],[c_495]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_4,plain,
% 1.66/0.99      ( ~ r2_hidden(X0,X1)
% 1.66/0.99      | m1_subset_1(X0,X2)
% 1.66/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 1.66/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_509,plain,
% 1.66/0.99      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
% 1.66/0.99      | ~ r2_hidden(X0,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.66/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_496,c_4]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_535,plain,
% 1.66/0.99      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
% 1.66/0.99      | ~ m1_subset_1(X1,X2)
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.66/0.99      | v1_xboole_0(X2)
% 1.66/0.99      | X0 != X1
% 1.66/0.99      | u1_struct_0(sK3) != X2 ),
% 1.66/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_509]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_536,plain,
% 1.66/0.99      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
% 1.66/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.66/0.99      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.66/0.99      inference(unflattening,[status(thm)],[c_535]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_681,plain,
% 1.66/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.66/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.66/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.66/0.99      | ~ m1_pre_topc(X4,X0)
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.66/0.99      | ~ m1_subset_1(X5,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.66/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.66/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.66/0.99      | ~ v1_funct_1(X2)
% 1.66/0.99      | ~ v2_pre_topc(X0)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | v2_struct_0(X4)
% 1.66/0.99      | ~ l1_pre_topc(X0)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.66/0.99      | X5 != X3
% 1.66/0.99      | u1_struct_0(sK3) != X6
% 1.66/0.99      | sK1 != X0 ),
% 1.66/0.99      inference(resolution_lifted,[status(thm)],[c_659,c_536]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_682,plain,
% 1.66/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.66/0.99      | r1_tmap_1(sK1,X1,X2,X3)
% 1.66/0.99      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.66/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.66/0.99      | ~ v1_funct_1(X2)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | ~ v2_pre_topc(sK1)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(sK1)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | ~ l1_pre_topc(sK1)
% 1.66/0.99      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.66/0.99      inference(unflattening,[status(thm)],[c_681]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_686,plain,
% 1.66/0.99      ( ~ l1_pre_topc(X1)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | ~ v1_funct_1(X2)
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
% 1.66/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.66/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.66/0.99      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.66/0.99      | r1_tmap_1(sK1,X1,X2,X3)
% 1.66/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.66/0.99      inference(global_propositional_subsumption,
% 1.66/0.99                [status(thm)],
% 1.66/0.99                [c_682,c_31,c_30,c_29]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_687,plain,
% 1.66/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.66/0.99      | r1_tmap_1(sK1,X1,X2,X3)
% 1.66/0.99      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.66/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.66/0.99      | ~ v1_funct_1(X2)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.66/0.99      inference(renaming,[status(thm)],[c_686]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_520,plain,
% 1.66/0.99      ( ~ m1_subset_1(X0,X1)
% 1.66/0.99      | m1_subset_1(X0,X2)
% 1.66/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.66/0.99      | v1_xboole_0(X1) ),
% 1.66/0.99      inference(resolution,[status(thm)],[c_2,c_4]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_720,plain,
% 1.66/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.66/0.99      | r1_tmap_1(sK1,X1,X2,X3)
% 1.66/0.99      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.66/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.66/0.99      | ~ v1_funct_1(X2)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.66/0.99      inference(forward_subsumption_resolution,
% 1.66/0.99                [status(thm)],
% 1.66/0.99                [c_687,c_520]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_922,plain,
% 1.66/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.66/0.99      | r1_tmap_1(sK1,X1,X2,X3)
% 1.66/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.66/0.99      | ~ v1_funct_1(X2)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.66/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.66/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.66/0.99      | sK2 != X2 ),
% 1.66/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_720]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_923,plain,
% 1.66/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.66/0.99      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.66/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.66/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.66/0.99      | ~ v1_funct_1(sK2)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.66/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.66/0.99      inference(unflattening,[status(thm)],[c_922]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_927,plain,
% 1.66/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
% 1.66/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.66/0.99      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.66/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.66/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.66/0.99      inference(global_propositional_subsumption,
% 1.66/0.99                [status(thm)],
% 1.66/0.99                [c_923,c_28]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_928,plain,
% 1.66/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.66/0.99      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.66/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.66/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.66/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.66/0.99      inference(renaming,[status(thm)],[c_927]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1128,plain,
% 1.66/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.66/0.99      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.66/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.66/0.99      | ~ v2_pre_topc(X1)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(X1)
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.66/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.66/0.99      | sK1 != sK1
% 1.66/0.99      | sK3 != X0 ),
% 1.66/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_928]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1129,plain,
% 1.66/0.99      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.66/0.99      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.66/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.66/0.99      | ~ v2_pre_topc(X0)
% 1.66/0.99      | v2_struct_0(X0)
% 1.66/0.99      | v2_struct_0(sK3)
% 1.66/0.99      | ~ l1_pre_topc(X0)
% 1.66/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.66/0.99      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.66/0.99      inference(unflattening,[status(thm)],[c_1128]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1049,plain,
% 1.66/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/0.99      | ~ l1_pre_topc(X1)
% 1.66/0.99      | sK1 != X1
% 1.66/0.99      | sK3 != X0 ),
% 1.66/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1050,plain,
% 1.66/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.66/0.99      | ~ l1_pre_topc(sK1) ),
% 1.66/0.99      inference(unflattening,[status(thm)],[c_1049]) ).
% 1.66/0.99  
% 1.66/0.99  cnf(c_1133,plain,
% 1.66/0.99      ( v2_struct_0(X0)
% 1.66/0.99      | ~ v2_pre_topc(X0)
% 1.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.66/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/0.99      | r1_tmap_1(sK1,X0,sK2,X1)
% 1.66/0.99      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.66/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.66/0.99      | ~ l1_pre_topc(X0)
% 1.66/1.00      | v1_xboole_0(u1_struct_0(sK3))
% 1.66/1.00      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.66/1.00      inference(global_propositional_subsumption,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_1129,c_29,c_25,c_1050]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1134,plain,
% 1.66/1.00      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.66/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.66/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.66/1.00      | ~ v2_pre_topc(X0)
% 1.66/1.00      | v2_struct_0(X0)
% 1.66/1.00      | ~ l1_pre_topc(X0)
% 1.66/1.00      | v1_xboole_0(u1_struct_0(sK3))
% 1.66/1.00      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.66/1.00      inference(renaming,[status(thm)],[c_1133]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1323,plain,
% 1.66/1.00      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.66/1.00      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.66/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.66/1.00      | v2_struct_0(X0)
% 1.66/1.00      | ~ l1_pre_topc(X0)
% 1.66/1.00      | v1_xboole_0(u1_struct_0(sK3))
% 1.66/1.00      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.66/1.00      | sK0 != X0 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_1134,c_33]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1324,plain,
% 1.66/1.00      ( r1_tmap_1(sK1,sK0,sK2,X0)
% 1.66/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.66/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.66/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.66/1.00      | v2_struct_0(sK0)
% 1.66/1.00      | ~ l1_pre_topc(sK0)
% 1.66/1.00      | v1_xboole_0(u1_struct_0(sK3))
% 1.66/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_1323]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1328,plain,
% 1.66/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.66/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.66/1.00      | r1_tmap_1(sK1,sK0,sK2,X0)
% 1.66/1.00      | v1_xboole_0(u1_struct_0(sK3))
% 1.66/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.66/1.00      inference(global_propositional_subsumption,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_1324,c_34,c_32,c_26]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1329,plain,
% 1.66/1.00      ( r1_tmap_1(sK1,sK0,sK2,X0)
% 1.66/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.66/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.66/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | v1_xboole_0(u1_struct_0(sK3))
% 1.66/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.66/1.00      inference(renaming,[status(thm)],[c_1328]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1442,plain,
% 1.66/1.00      ( r1_tmap_1(sK1,sK0,sK2,X0)
% 1.66/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.66/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.66/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.66/1.00      inference(backward_subsumption_resolution,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_1428,c_1329]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1525,plain,
% 1.66/1.00      ( r1_tmap_1(sK1,sK0,sK2,X0)
% 1.66/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.66/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.66/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.66/1.00      inference(equality_resolution_simp,[status(thm)],[c_1442]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2070,plain,
% 1.66/1.00      ( r1_tmap_1(sK1,sK0,sK2,X0) = iProver_top
% 1.66/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) != iProver_top
% 1.66/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 1.66/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_1525]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1,plain,
% 1.66/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.66/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2085,plain,
% 1.66/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_0,plain,
% 1.66/1.00      ( k2_subset_1(X0) = X0 ),
% 1.66/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2095,plain,
% 1.66/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.66/1.00      inference(light_normalisation,[status(thm)],[c_2085,c_0]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2174,plain,
% 1.66/1.00      ( r1_tmap_1(sK1,sK0,sK2,X0) = iProver_top
% 1.66/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) != iProver_top
% 1.66/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 1.66/1.00      inference(forward_subsumption_resolution,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_2070,c_2095]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2599,plain,
% 1.66/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
% 1.66/1.00      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 1.66/1.00      inference(superposition,[status(thm)],[c_2292,c_2174]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(contradiction,plain,
% 1.66/1.00      ( $false ),
% 1.66/1.00      inference(minisat,[status(thm)],[c_2599,c_2286,c_48]) ).
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.66/1.00  
% 1.66/1.00  ------                               Statistics
% 1.66/1.00  
% 1.66/1.00  ------ General
% 1.66/1.00  
% 1.66/1.00  abstr_ref_over_cycles:                  0
% 1.66/1.00  abstr_ref_under_cycles:                 0
% 1.66/1.00  gc_basic_clause_elim:                   0
% 1.66/1.00  forced_gc_time:                         0
% 1.66/1.00  parsing_time:                           0.01
% 1.66/1.00  unif_index_cands_time:                  0.
% 1.66/1.00  unif_index_add_time:                    0.
% 1.66/1.00  orderings_time:                         0.
% 1.66/1.00  out_proof_time:                         0.02
% 1.66/1.00  total_time:                             0.115
% 1.66/1.00  num_of_symbols:                         59
% 1.66/1.00  num_of_terms:                           1542
% 1.66/1.00  
% 1.66/1.00  ------ Preprocessing
% 1.66/1.00  
% 1.66/1.00  num_of_splits:                          2
% 1.66/1.00  num_of_split_atoms:                     2
% 1.66/1.00  num_of_reused_defs:                     0
% 1.66/1.00  num_eq_ax_congr_red:                    11
% 1.66/1.00  num_of_sem_filtered_clauses:            1
% 1.66/1.00  num_of_subtypes:                        0
% 1.66/1.00  monotx_restored_types:                  0
% 1.66/1.00  sat_num_of_epr_types:                   0
% 1.66/1.00  sat_num_of_non_cyclic_types:            0
% 1.66/1.00  sat_guarded_non_collapsed_types:        0
% 1.66/1.00  num_pure_diseq_elim:                    0
% 1.66/1.00  simp_replaced_by:                       0
% 1.66/1.00  res_preprocessed:                       106
% 1.66/1.00  prep_upred:                             0
% 1.66/1.00  prep_unflattend:                        41
% 1.66/1.00  smt_new_axioms:                         0
% 1.66/1.00  pred_elim_cands:                        2
% 1.66/1.00  pred_elim:                              13
% 1.66/1.00  pred_elim_cl:                           17
% 1.66/1.00  pred_elim_cycles:                       20
% 1.66/1.00  merged_defs:                            8
% 1.66/1.00  merged_defs_ncl:                        0
% 1.66/1.00  bin_hyper_res:                          8
% 1.66/1.00  prep_cycles:                            4
% 1.66/1.00  pred_elim_time:                         0.029
% 1.66/1.00  splitting_time:                         0.
% 1.66/1.00  sem_filter_time:                        0.
% 1.66/1.00  monotx_time:                            0.
% 1.66/1.00  subtype_inf_time:                       0.
% 1.66/1.00  
% 1.66/1.00  ------ Problem properties
% 1.66/1.00  
% 1.66/1.00  clauses:                                19
% 1.66/1.00  conjectures:                            6
% 1.66/1.00  epr:                                    1
% 1.66/1.00  horn:                                   18
% 1.66/1.00  ground:                                 9
% 1.66/1.00  unary:                                  7
% 1.66/1.00  binary:                                 3
% 1.66/1.00  lits:                                   44
% 1.66/1.00  lits_eq:                                4
% 1.66/1.00  fd_pure:                                0
% 1.66/1.00  fd_pseudo:                              0
% 1.66/1.00  fd_cond:                                0
% 1.66/1.00  fd_pseudo_cond:                         0
% 1.66/1.00  ac_symbols:                             0
% 1.66/1.00  
% 1.66/1.00  ------ Propositional Solver
% 1.66/1.00  
% 1.66/1.00  prop_solver_calls:                      25
% 1.66/1.00  prop_fast_solver_calls:                 1020
% 1.66/1.00  smt_solver_calls:                       0
% 1.66/1.00  smt_fast_solver_calls:                  0
% 1.66/1.00  prop_num_of_clauses:                    558
% 1.66/1.00  prop_preprocess_simplified:             2829
% 1.66/1.00  prop_fo_subsumed:                       44
% 1.66/1.00  prop_solver_time:                       0.
% 1.66/1.00  smt_solver_time:                        0.
% 1.66/1.00  smt_fast_solver_time:                   0.
% 1.66/1.00  prop_fast_solver_time:                  0.
% 1.66/1.00  prop_unsat_core_time:                   0.
% 1.66/1.00  
% 1.66/1.00  ------ QBF
% 1.66/1.00  
% 1.66/1.00  qbf_q_res:                              0
% 1.66/1.00  qbf_num_tautologies:                    0
% 1.66/1.00  qbf_prep_cycles:                        0
% 1.66/1.00  
% 1.66/1.00  ------ BMC1
% 1.66/1.00  
% 1.66/1.00  bmc1_current_bound:                     -1
% 1.66/1.00  bmc1_last_solved_bound:                 -1
% 1.66/1.00  bmc1_unsat_core_size:                   -1
% 1.66/1.00  bmc1_unsat_core_parents_size:           -1
% 1.66/1.00  bmc1_merge_next_fun:                    0
% 1.66/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.66/1.00  
% 1.66/1.00  ------ Instantiation
% 1.66/1.00  
% 1.66/1.00  inst_num_of_clauses:                    111
% 1.66/1.00  inst_num_in_passive:                    29
% 1.66/1.00  inst_num_in_active:                     63
% 1.66/1.00  inst_num_in_unprocessed:                19
% 1.66/1.00  inst_num_of_loops:                      70
% 1.66/1.00  inst_num_of_learning_restarts:          0
% 1.66/1.00  inst_num_moves_active_passive:          5
% 1.66/1.00  inst_lit_activity:                      0
% 1.66/1.00  inst_lit_activity_moves:                0
% 1.66/1.00  inst_num_tautologies:                   0
% 1.66/1.00  inst_num_prop_implied:                  0
% 1.66/1.00  inst_num_existing_simplified:           0
% 1.66/1.00  inst_num_eq_res_simplified:             0
% 1.66/1.00  inst_num_child_elim:                    0
% 1.66/1.00  inst_num_of_dismatching_blockings:      2
% 1.66/1.00  inst_num_of_non_proper_insts:           53
% 1.66/1.00  inst_num_of_duplicates:                 0
% 1.66/1.00  inst_inst_num_from_inst_to_res:         0
% 1.66/1.00  inst_dismatching_checking_time:         0.
% 1.66/1.00  
% 1.66/1.00  ------ Resolution
% 1.66/1.00  
% 1.66/1.00  res_num_of_clauses:                     0
% 1.66/1.00  res_num_in_passive:                     0
% 1.66/1.00  res_num_in_active:                      0
% 1.66/1.00  res_num_of_loops:                       110
% 1.66/1.00  res_forward_subset_subsumed:            9
% 1.66/1.00  res_backward_subset_subsumed:           0
% 1.66/1.00  res_forward_subsumed:                   0
% 1.66/1.00  res_backward_subsumed:                  0
% 1.66/1.00  res_forward_subsumption_resolution:     4
% 1.66/1.00  res_backward_subsumption_resolution:    2
% 1.66/1.00  res_clause_to_clause_subsumption:       136
% 1.66/1.00  res_orphan_elimination:                 0
% 1.66/1.00  res_tautology_del:                      21
% 1.66/1.00  res_num_eq_res_simplified:              2
% 1.66/1.00  res_num_sel_changes:                    0
% 1.66/1.00  res_moves_from_active_to_pass:          0
% 1.66/1.00  
% 1.66/1.00  ------ Superposition
% 1.66/1.00  
% 1.66/1.00  sup_time_total:                         0.
% 1.66/1.00  sup_time_generating:                    0.
% 1.66/1.00  sup_time_sim_full:                      0.
% 1.66/1.00  sup_time_sim_immed:                     0.
% 1.66/1.00  
% 1.66/1.00  sup_num_of_clauses:                     20
% 1.66/1.00  sup_num_in_active:                      13
% 1.66/1.00  sup_num_in_passive:                     7
% 1.66/1.00  sup_num_of_loops:                       12
% 1.66/1.00  sup_fw_superposition:                   3
% 1.66/1.00  sup_bw_superposition:                   0
% 1.66/1.00  sup_immediate_simplified:               0
% 1.66/1.00  sup_given_eliminated:                   0
% 1.66/1.00  comparisons_done:                       0
% 1.66/1.00  comparisons_avoided:                    0
% 1.66/1.00  
% 1.66/1.00  ------ Simplifications
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  sim_fw_subset_subsumed:                 0
% 1.66/1.00  sim_bw_subset_subsumed:                 0
% 1.66/1.00  sim_fw_subsumed:                        0
% 1.66/1.00  sim_bw_subsumed:                        0
% 1.66/1.00  sim_fw_subsumption_res:                 2
% 1.66/1.00  sim_bw_subsumption_res:                 0
% 1.66/1.00  sim_tautology_del:                      1
% 1.66/1.00  sim_eq_tautology_del:                   0
% 1.66/1.00  sim_eq_res_simp:                        0
% 1.66/1.00  sim_fw_demodulated:                     0
% 1.66/1.00  sim_bw_demodulated:                     0
% 1.66/1.00  sim_light_normalised:                   4
% 1.66/1.00  sim_joinable_taut:                      0
% 1.66/1.00  sim_joinable_simp:                      0
% 1.66/1.00  sim_ac_normalised:                      0
% 1.66/1.00  sim_smt_subsumption:                    0
% 1.66/1.00  
%------------------------------------------------------------------------------
